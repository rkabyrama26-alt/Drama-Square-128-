import 'dotenv/config';
import express from 'express';
import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';
import type {
  AppLocale,
  DurationFilter,
  SearchType,
  ServerHealthResponse,
  SortOrder,
  TikTokCategory,
  TrendingCategory,
} from './src/shared/types.ts';
import {
  downloadVideoAsMp4,
  getMediaCacheStats,
  getMediaChannelDetails,
  getMediaVideoDetails,
  getSuggestQueries,
  getTrendingMediaVideos,
  proxyHlsResource,
  resolveVideoPlayback,
  searchMediaVideos,
  streamDirectVideoMp4,
  streamVideoMasterManifest,
} from './src/server/mediaService.ts';
import {
  getTikTokFeed,
  proxyoutubeikTokImage,
  searchTikTokReels,
  streamTikTokVideo,
} from './src/server/tiktokService.ts';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const PORT = Number.parseInt(process.env.PORT || '3000', 10);
const startedAt = Date.now();

const VALID_SORTS = new Set<SortOrder>(['relevance', 'date', 'views', 'rating']);
const VALID_TYPES = new Set<SearchType>(['all', 'video', 'live', 'short']);
const VALID_DURATIONS = new Set<DurationFilter>(['any', 'short', 'medium', 'long']);
const VALID_CATEGORIES = new Set<TrendingCategory>(['all', 'tech', 'music', 'gaming', 'education', 'news']);
const VALID_TIKTOK_CATEGORIES = new Set<TikTokCategory>(['all', 'comedy', 'gaming', 'sports', 'music', 'food']);

async function startServer() {
  const app = express();
  app.use(express.json());

  app.use('/api', (_req, res, next) => {
    res.setHeader('Access-Control-Allow-Origin', '*');
    res.setHeader('Access-Control-Allow-Methods', 'GET, OPTIONS');
    res.setHeader('Access-Control-Allow-Headers', 'Content-Type, Range, User-Agent');
    next();
  });

  app.get('/api/health', (_req, res) => {
    const payload: ServerHealthResponse = {
      status: 'ok',
      service: 'Drama Square Media Server',
      uptimeSeconds: Math.floor((Date.now() - startedAt) / 1000),
      cacheEntries: getMediaCacheStats().entries,
    };
    res.json(payload);
  });

  // Independent Video Server Routes
  app.get('/api/videos/trending', async (req, res) => {
    try {
      const catRaw = String(req.query.category || 'all') as TrendingCategory;
      const hl: AppLocale = req.query.hl === 'en' ? 'en' : 'ar';
      const refresh = req.query.refresh === '1' || req.query.refresh === 'true';
      const seedRaw = Number(req.query.seed);
      const seed = Number.isFinite(seedRaw) ? seedRaw : undefined;
      const category = VALID_CATEGORIES.has(catRaw) ? catRaw : 'all';
      const data = await getTrendingMediaVideos(category, hl, { refresh, seed });
      return res.json(data);
    } catch (err) {
      return res.status(500).json({
        error: err instanceof Error ? err.message : 'Trending fetch failed',
      });
    }
  });

  app.get('/api/videos/search', async (req, res) => {
    try {
      const q = String(req.query.q || '').trim();
      const continuation = String(req.query.continuation || '').trim();
      if (!q && !continuation) {
        return res.status(400).json({
          error: 'Missing required query parameter: q',
        });
      }

      const sortRaw = String(req.query.sort || 'relevance') as SortOrder;
      const typeRaw = String(req.query.type || 'all') as SearchType;
      const durationRaw = String(req.query.duration || 'any') as DurationFilter;
      const hl: AppLocale = req.query.hl === 'en' ? 'en' : 'ar';

      const data = await searchMediaVideos({
        query: q,
        sort: VALID_SORTS.has(sortRaw) ? sortRaw : 'relevance',
        type: VALID_TYPES.has(typeRaw) ? typeRaw : 'all',
        duration: VALID_DURATIONS.has(durationRaw) ? durationRaw : 'any',
        continuation: continuation || undefined,
        hl,
      });

      return res.json(data);
    } catch (err) {
      return res.status(500).json({
        error: err instanceof Error ? err.message : 'Search failed',
      });
    }
  });

  app.get('/api/videos/suggest', async (req, res) => {
    try {
      const q = String(req.query.q || '').trim();
      const hl: AppLocale = req.query.hl === 'en' ? 'en' : 'ar';
      const data = await getSuggestQueries(q, hl);
      return res.json(data);
    } catch (err) {
      return res.status(500).json({
        error: err instanceof Error ? err.message : 'Suggest failed',
      });
    }
  });

  // تعديل مسار الـ HLS لحقن الترويسات وتجاوز خطأ 403
  app.get('/api/videos/hls', async (req, res) => {
    try {
      const targetUrl = String(req.query.u || '').trim();
      const rangeHeader = typeof req.headers.range === 'string' ? req.headers.range : undefined;
      
      // فرض ترويسات متصفح حقيقي لمنع الحظر
      req.headers['user-agent'] = req.headers['user-agent'] || 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36';
      
      await proxyHlsResource(targetUrl, rangeHeader, res);
    } catch (err) {
      if (!res.headersSent) {
        res.status(500).json({
          error: err instanceof Error ? err.message : 'Stream proxy failed',
        });
      }
    }
  });

  app.get('/api/videos/item/:id/resolve', async (req, res) => {
    try {
      const id = String(req.params.id || '').trim();
      const hl: AppLocale = req.query.hl === 'en' ? 'en' : 'ar';
      const titleHint = String(req.query.title || '').trim();
      const resolved = await resolveVideoPlayback(id, hl, { titleHint });
      return res.json(resolved);
    } catch (err) {
      return res.json({
        playable: false,
        code: 'RESOLVE_ERROR',
        reason: err instanceof Error ? err.message : 'Stream resolution failed',
      });
    }
  });

  app.get('/api/videos/item/:id/media.mp4', async (req, res) => {
    try {
      const id = String(req.params.id || '').trim();
      req.headers['user-agent'] = req.headers['user-agent'] || 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36';
      await streamDirectVideoMp4(id, req, res);
    } catch (err) {
      if (!res.headersSent) {
        res.status(500).json({
          error: err instanceof Error ? err.message : 'Stream unavailable',
        });
      }
    }
  });

  app.get('/api/videos/item/:id/stream.m3u8', async (req, res) => {
    try {
      const id = String(req.params.id || '').trim();
      await streamVideoMasterManifest(id, res);
    } catch (err) {
      if (!res.headersSent) {
        res.status(500).json({
          error: err instanceof Error ? err.message : 'Stream unavailable',
        });
      }
    }
  });

  app.get('/api/videos/item/:id/download.mp4', async (req, res) => {
    try {
      const id = String(req.params.id || '').trim();
      await downloadVideoAsMp4(id, req, res);
    } catch (err) {
      if (!res.headersSent) {
        res.status(500).json({
          error: err instanceof Error ? err.message : 'MP4 download unavailable',
        });
      }
    }
  });

  app.get('/api/videos/item/:id', async (req, res) => {
    try {
      const id = String(req.params.id || '').trim();
      const hl: AppLocale = req.query.hl === 'en' ? 'en' : 'ar';
      const data = await getMediaVideoDetails(id, hl);
      if (!data) {
        return res.status(404).json({ error: 'Video not found' });
      }
      return res.json(data);
    } catch (err) {
      return res.status(500).json({
        error: err instanceof Error ? err.message : 'Video lookup failed',
      });
    }
  });

  app.get('/api/videos/channel/:id', async (req, res) => {
    try {
      const id = String(req.params.id || '').trim();
      const hl: AppLocale = req.query.hl === 'en' ? 'en' : 'ar';
      const data = await getMediaChannelDetails(id, hl);
      if (!data) {
        return res.status(404).json({ error: 'Channel not found' });
      }
      return res.json(data);
    } catch (err) {
      return res.status(500).json({
        error: err instanceof Error ? err.message : 'Channel lookup failed',
      });
    }
  });

  // Dedicated TikTok Server Routes (Feed + Search + Video/Image Proxy) for Shorts section ONLY
  app.get('/api/tiktok/feed', async (req, res) => {
    try {
      const catRaw = String(req.query.category || 'all') as TikTokCategory;
      const category = VALID_TIKTOK_CATEGORIES.has(catRaw) ? catRaw : 'all';
      const forceRefresh = req.query.refresh === '1' || req.query.refresh === 'true';
      const data = await getTikTokFeed(category, forceRefresh);
      return res.json(data);
    } catch (err) {
      return res.status(500).json({
        error: err instanceof Error ? err.message : 'TikTok server feed failed',
      });
    }
  });

  app.get('/api/tiktok/search', async (req, res) => {
    try {
      const q = String(req.query.q || '').trim();
      const data = await searchTikTokReels(q);
      return res.json(data);
    } catch (err) {
      return res.status(500).json({
        error: err instanceof Error ? err.message : 'TikTok search failed',
      });
    }
  });

  app.get('/api/tiktok/stream/:id', async (req, res) => {
    try {
      const id = String(req.params.id || '').trim();
      const rangeHeader = typeof req.headers.range === 'string' ? req.headers.range : undefined;
      const asDownload = req.query.download === '1';
      await streamTikTokVideo(id, rangeHeader, asDownload, res);
    } catch (err) {
      if (!res.headersSent) {
        res.status(500).json({
          error: err instanceof Error ? err.message : 'TikTok stream failed',
        });
      }
    }
  });

  app.get('/api/tiktok/cover/:id', async (req, res) => {
    const id = String(req.params.id || '').trim();
    await proxyoutubeikTokImage(id, 'cover', res);
  });

  app.get('/api/tiktok/avatar/:id', async (req, res) => {
    const id = String(req.params.id || '').trim();
    await proxyoutubeikTokImage(id, 'avatar', res);
  });

  const isProd = process.env.NODE_ENV === 'production';
  const distDir = path.resolve(__dirname, 'dist');

  if (!isProd) {
    const { createServer: createViteServer } = await import('vite');
    const vite = await createViteServer({
      server: { middlewareMode: true },
      appType: 'spa',
    });
    app.use(vite.middlewares);
  } else if (fs.existsSync(distDir)) {
    app.use(express.static(distDir));
    app.get('*', (_req, res) => {
      res.sendFile(path.join(distDir, 'index.html'));
    });
  }

  app.listen(PORT, '0.0.0.0', () => {
    console.log(`Drama Square Server listening on http://0.0.0.0:${PORT}`);
  });
}

startServer();
