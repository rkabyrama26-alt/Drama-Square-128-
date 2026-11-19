import type { Request, Response } from 'express';
import { execFile, spawn } from 'node:child_process';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { Readable } from 'node:stream';
import type { ReadableStream as NodeReadableStream } from 'node:stream/web';
import { promisify } from 'node:util';
import vm from 'node:vm';
import { Innertube, Log, Platform, type Types } from 'youtubei.js';
import type {
  AppLocale,
  ChannelResponse,
  DurationFilter,
  MediaChannelSummary,
  MediaComment,
  MediaVideo,
  SearchResponse,
  SearchType,
  SortOrder,
  SuggestResponse,
  TrendingCategory,
  TrendingResponse,
  VideoDetailsResponse,
} from '../shared/types.ts';
import {
  buildFallbackSearchQueries,
  extractMediaId,
  formatSubscribersText,
  isAllowedStreamHost,
  normalizeGlobalQuery,
  parseMediaChannel,
  parseMediaVideo,
  pickDownloadVariantUrl,
  prioritizeFreshRawVideos,
  rankSearchChannels,
  rewriteM3u8Manifest,
  rotateFreshBatches,
  sanitizeDownloadFilename,
  stripHtmlTags,
  type RawDailymotionUser,
  type RawDailymotionVideo,
} from './mediaParser.ts';
import {
  isYouTubeVideoId,
  parseYouTubeChannelSummary,
  parseYouTubeCommentNode,
  parseYouTubeVideoNode,
  pickBestThumbnail,
  scoreStreamCandidateMatch,
} from './youtubeParser.ts';
import {
  matchLiveBroadcastStream,
  parseM3uLivePlaylist,
  type LiveChannelEntry,
} from './liveMatcher.ts';

const execFileAsync = promisify(execFile);

// Keep youtubei.js parser logs silent so JIT schema drift warnings never pollute server logs
Log.setLevel(Log.Level.NONE);

// Register JS evaluator required by youtubei.js for player signature & n-parameter deciphering
Platform.shim.eval = async (
  data: Types.BuildScriptResult,
  env: Record<string, Types.VMPrimative>,
) => {
  const properties: string[] = [];
  if (env.n) properties.push(`n: exportedVars.nFunction(${JSON.stringify(String(env.n))})`);
  if (env.sig) properties.push(`sig: exportedVars.sigFunction(${JSON.stringify(String(env.sig))})`);
  const code = `${data.output}\nreturn { ${properties.join(', ')} };`;
  return vm.runInNewContext(`(function(){${code}})()`);
};

const DM_API_BASE = 'https://api.dailymotion.com';
const DESKTOP_UA =
  'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36';
const VR_UA =
  'com.google.android.apps.youtube.vr.oculus/1.60.19 (Linux; U; Android 12L; eureka-user Build/SQ3A.220605.009.A1) gzip';

const DM_VIDEO_FIELDS = [
  'id',
  'title',
  'description',
  'duration',
  'views_total',
  'likes_total',
  'created_time',
  'mode',
  'onair',
  'status',
  'thumbnail_720_url',
  'thumbnail_480_url',
  'thumbnail_360_url',
  'owner.id',
  'owner.screenname',
  'owner.username',
  'owner.avatar_120_url',
  'owner.followers_total',
  'owner.verified',
].join(',');

const DM_USER_FIELDS = [
  'id',
  'screenname',
  'username',
  'avatar_120_url',
  'avatar_360_url',
  'cover_250_url',
  'description',
  'followers_total',
  'videos_total',
  'verified',
].join(',');

interface CacheEntry<T> {
  value: T;
  expiresAt: number;
}

export interface StreamResolutionResult {
  playable: boolean;
  kind?: 'mp4' | 'hls';
  url?: string;
  upstreamUrl?: string;
  dmId?: string;
  title?: string;
  code?: string;
  reason?: string;
}

const cache = new Map<string, CacheEntry<unknown>>();
// eslint-disable-next-line @typescript-eslint/no-explicit-any
const searchContinuationStore = new Map<string, { searchObj: any; expiresAt: number }>();
const CACHE_TTL_MS = 5 * 60 * 1000;

function getCached<T>(key: string): T | null {
  const entry = cache.get(key);
  if (!entry) return null;
  if (Date.now() > entry.expiresAt) {
    cache.delete(key);
    return null;
  }
  return entry.value as T;
}

function setCached<T>(key: string, value: T, ttlMs = CACHE_TTL_MS): void {
  if (cache.size > 400) {
    const oldest = cache.keys().next().value;
    if (oldest) cache.delete(oldest);
  }
  cache.set(key, { value, expiresAt: Date.now() + ttlMs });
}

export function getMediaCacheStats(): { entries: number } {
  return { entries: cache.size };
}

const catalogClientPromises = new Map<string, Promise<Innertube>>();
const playerClientPromises = new Map<string, Promise<Innertube>>();

let ytStreamProbe: { playable: boolean; expiresAt: number; inFlight?: Promise<boolean> } | null = null;

function hasPlausibleYouTubeCookies(): boolean {
  const raw = process.env.YT_COOKIES?.trim() || '';
  if (!raw || raw.length < 20) return false;
  return raw.includes('=') && (raw.includes('SID') || raw.includes(';'));
}

async function canUseYouTubeStreams(hl: AppLocale = 'ar'): Promise<boolean> {
  if (!hasPlausibleYouTubeCookies()) return false;
  const now = Date.now();
  if (ytStreamProbe && ytStreamProbe.expiresAt > now) {
    return ytStreamProbe.playable;
  }
  if (ytStreamProbe?.inFlight) {
    return ytStreamProbe.inFlight;
  }

  const probePromise = (async () => {
    try {
      // Probe a known stable YouTube video ID with the configured session/cookies
      const res = await tryResolveDirectYouTubeStream('dQw4w9WgXcQ', hl);
      const ok = Boolean(res?.upstreamUrl);
      ytStreamProbe = {
        playable: ok,
        expiresAt: Date.now() + (ok ? 10 * 60 * 1000 : 15 * 60 * 1000),
      };
      return ok;
    } catch {
      ytStreamProbe = { playable: false, expiresAt: Date.now() + 15 * 60 * 1000 };
      return false;
    }
  })();

  ytStreamProbe = { playable: false, expiresAt: 0, inFlight: probePromise };
  return probePromise;
}

function getRegionForLocale(hl: AppLocale): string {
  if (hl === 'ar') {
    const raw = (process.env.YOUTUBE_COUNTRY || 'IQ').trim().toUpperCase();
    return /^[A-Z]{2}$/.test(raw) ? raw : 'IQ';
  }
  return 'US';
}

function resetYoutubeCatalogClient(hl: AppLocale): void {
  catalogClientPromises.delete(`cat:${hl}`);
}

function createFreshCatalogClient(lang: 'ar' | 'en', location: string): Promise<Innertube> {
  return Innertube.create({
    retrieve_player: false,
    lang,
    location,
    generate_session_locally: true,
  });
}

function getYoutubeCatalogClient(hl: AppLocale): Promise<Innertube> {
  const key = `cat:${hl}`;
  const existing = catalogClientPromises.get(key);
  if (existing) return existing;

  const created = createFreshCatalogClient(
    hl === 'en' ? 'en' : 'ar',
    getRegionForLocale(hl),
  ).catch((err) => {
    catalogClientPromises.delete(key);
    throw err;
  });

  catalogClientPromises.set(key, created);
  return created;
}

async function runWithCatalogClient<T>(
  hl: AppLocale,
  fn: (yt: Innertube) => Promise<T>,
  shouldRetryEmpty?: (result: T) => boolean,
): Promise<T> {
  try {
    const client = await getYoutubeCatalogClient(hl);
    const result = await fn(client);
    if (!shouldRetryEmpty || !shouldRetryEmpty(result)) {
      return result;
    }
  } catch {
    // Fall through to reset & retry
  }

  resetYoutubeCatalogClient(hl);
  try {
    const client = await getYoutubeCatalogClient(hl);
    const retried = await fn(client);
    if (!shouldRetryEmpty || !shouldRetryEmpty(retried)) {
      return retried;
    }
  } catch {
    // Fall through to clean US/en locale fallback (avoids YouTube browse 400 on some IQ/ar sessions)
  }

  const fallbackClient = await getYoutubeCatalogClient('en');
  return await fn(fallbackClient);
}

function getYoutubePlayerClient(hl: AppLocale): Promise<Innertube> {
  const key = `play:${hl}`;
  const existing = playerClientPromises.get(key);
  if (existing) return existing;

  const created = Innertube.create({
    retrieve_player: true,
    lang: hl === 'en' ? 'en' : 'ar',
    location: getRegionForLocale(hl),
    generate_session_locally: true,
    cookie: hasPlausibleYouTubeCookies() ? process.env.YT_COOKIES?.trim() : undefined,
  }).catch((err) => {
    playerClientPromises.delete(key);
    throw err;
  });

  playerClientPromises.set(key, created);
  return created;
}

async function fetchDailymotionJson<T>(pathAndQuery: string, timeoutMs = 8000): Promise<T> {
  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), timeoutMs);
  try {
    const res = await fetch(`${DM_API_BASE}${pathAndQuery}`, {
      headers: { 'User-Agent': DESKTOP_UA, Accept: 'application/json' },
      signal: controller.signal,
    });
    if (!res.ok) {
      throw new Error(`Media API HTTP ${res.status}`);
    }
    return (await res.json()) as T;
  } finally {
    clearTimeout(timer);
  }
}

const SPAM_AD_PATTERN = /شقة للبيع|مزرعة للبيع|عقارات للبيع|ارض للبيع|فيلا للبيع/i;

function filterCleanRawVideos(list: RawDailymotionVideo[]): RawDailymotionVideo[] {
  return list.filter((item) => {
    const title = String(item?.title || '').trim();
    const id = String(item?.id || '').trim();
    const status = String((item as RawDailymotionVideo & { status?: string })?.status || '').toLowerCase();
    if (!id || !title) return false;
    if (status && status !== 'published') return false;
    if (SPAM_AD_PATTERN.test(title)) return false;
    return true;
  });
}

function interleaveMediaVideos(batches: MediaVideo[][], limit = 60): MediaVideo[] {
  const out: MediaVideo[] = [];
  const seen = new Set<string>();
  const maxLen = Math.max(0, ...batches.map((b) => b.length));

  for (let i = 0; i < maxLen; i += 1) {
    for (const batch of batches) {
      const item = batch[i];
      if (!item || seen.has(item.id)) continue;
      seen.add(item.id);
      out.push(item);
      if (out.length >= limit) return out;
    }
  }
  return out;
}

const YT_TRENDING_QUERIES: Record<
  TrendingCategory,
  { ar: Array<{ q: string; upload_date?: 'today' | 'week' | 'month' }>; en: Array<{ q: string; upload_date?: 'today' | 'week' | 'month' }> }
> = {
  all: {
    ar: [
      { q: 'مسلسل عراقي جديد 2026', upload_date: 'week' },
      { q: 'مسلسلات عربية جديدة 2026', upload_date: 'week' },
      { q: 'ترند العراق اليوم', upload_date: 'today' },
      { q: 'أغاني عربية جديدة 2026', upload_date: 'week' },
      { q: 'أخبار العراق اليوم', upload_date: 'today' },
    ],
    en: [
      { q: 'new drama series trailer 2026', upload_date: 'week' },
      { q: 'trending music video 2026', upload_date: 'week' },
      { q: 'world news today', upload_date: 'today' },
      { q: 'gaming tech review 2026', upload_date: 'week' },
    ],
  },
  tech: {
    ar: [
      { q: 'مراجعة هواتف تقنية 2026', upload_date: 'week' },
      { q: 'الذكاء الاصطناعي برمجة 2026', upload_date: 'week' },
    ],
    en: [
      { q: 'smartphone tech review 2026', upload_date: 'week' },
      { q: 'ai software developer 2026', upload_date: 'week' },
    ],
  },
  music: {
    ar: [
      { q: 'أغاني عربية جديدة 2026', upload_date: 'week' },
      { q: 'أغاني عراقية جديدة 2026', upload_date: 'week' },
    ],
    en: [
      { q: 'new official music video 2026', upload_date: 'week' },
      { q: 'top music hits 2026', upload_date: 'week' },
    ],
  },
  gaming: {
    ar: [
      { q: 'تختيم ألعاب فيديو جديدة 2026', upload_date: 'week' },
      { q: 'ببجي وجي تي اي 2026', upload_date: 'today' },
    ],
    en: [
      { q: 'new game walkthrough gameplay 2026', upload_date: 'week' },
      { q: 'gaming highlights today', upload_date: 'today' },
    ],
  },
  education: {
    ar: [
      { q: 'وثائقي علوم وتاريخ 2026', upload_date: 'month' },
      { q: 'دروس وتعلم لغات برمجة', upload_date: 'week' },
    ],
    en: [
      { q: 'science documentary 2026', upload_date: 'month' },
      { q: 'educational lecture course', upload_date: 'week' },
    ],
  },
  news: {
    ar: [
      { q: 'نشرة أخبار العراق اليوم مباشر', upload_date: 'today' },
      { q: 'أخبار العالم العاجلة اليوم', upload_date: 'today' },
    ],
    en: [
      { q: 'world breaking news today', upload_date: 'today' },
      { q: 'live news report today', upload_date: 'today' },
    ],
  },
};

let trendingRotationCounter = 0;

function buildFreshPlayableTrendingPaths(
  category: TrendingCategory,
  hl: AppLocale,
  variantSeed = 0,
): string[] {
  const days60 = Math.floor(Date.now() / 1000) - 60 * 86400;
  const days14 = Math.floor(Date.now() / 1000) - 14 * 86400;
  const baseFields = encodeURIComponent(DM_VIDEO_FIELDS);
  const langParam = hl === 'ar' ? '&languages=ar' : '&languages=en';
  const dmPage = (Math.abs(variantSeed) % 3) + 1;

  if (hl === 'ar') {
    switch (category) {
      case 'tech':
        return [
          `/videos?fields=${baseFields}&limit=16&page=${dmPage}&channel=tech&created_after=${days60}&sort=visited-month`,
          `/videos?fields=${baseFields}&limit=14&created_after=${days60}&sort=relevance&search=${encodeURIComponent('الذكاء الاصطناعي تقنية')}`,
          `/videos?fields=${baseFields}&limit=12&channel=tech&sort=recent`,
        ];
      case 'music':
        return [
          `/videos?fields=${baseFields}&limit=16&page=${dmPage}&channel=music${langParam}&created_after=${days60}&sort=visited-month`,
          `/videos?fields=${baseFields}&limit=14&created_after=${days60}&sort=relevance&search=${encodeURIComponent('اغنية عربية جديدة')}`,
          `/videos?fields=${baseFields}&limit=12&channel=music${langParam}&sort=recent`,
        ];
      case 'gaming':
        return [
          `/videos?fields=${baseFields}&limit=16&page=${dmPage}&created_after=${days60}&sort=relevance&search=${encodeURIComponent('ببجي موبايل لعبة')}`,
          `/videos?fields=${baseFields}&limit=16&channel=videogames&created_after=${days60}&sort=visited-month`,
          `/videos?fields=${baseFields}&limit=12&channel=videogames&sort=recent`,
        ];
      case 'education':
        return [
          `/videos?fields=${baseFields}&limit=16&page=${dmPage}&created_after=${days60}&sort=relevance&search=${encodeURIComponent('وثائقي تاريخ علوم')}`,
          `/videos?fields=${baseFields}&limit=16&channel=school&created_after=${days60}&sort=visited-month`,
          `/videos?fields=${baseFields}&limit=12&channel=school&sort=recent`,
        ];
      case 'news':
        return [
          `/videos?fields=${baseFields}&limit=16&page=${dmPage}&channel=news${langParam}&created_after=${days60}&sort=recent`,
          `/videos?fields=${baseFields}&limit=16&created_after=${days60}&sort=relevance&search=${encodeURIComponent('اخبار العراق اليوم')}`,
          `/videos?fields=${baseFields}&limit=12&channel=news${langParam}&sort=visited-week`,
        ];
      case 'all':
      default: {
        const allTopics = [
          'مسلسل عراقي 2026',
          'مسلسلات عربية جديدة',
          'برامج عربية 2026',
          'العراق بغداد اليوم',
          'أفلام عربية جديدة',
          'دراما خليجية ومصرية',
          'كوميديا ومقالب عربية',
          'رياضة وكرة قدم اليوم',
        ];
        const idxA = Math.abs(variantSeed) % allTopics.length;
        const idxB = (idxA + 2) % allTopics.length;
        const idxC = (idxA + 4) % allTopics.length;
        return [
          `/videos?fields=${baseFields}&limit=16&page=${dmPage}${langParam}&created_after=${days14}&sort=recent`,
          `/videos?fields=${baseFields}&limit=16&page=${dmPage}${langParam}&created_after=${days60}&sort=visited-week`,
          `/videos?fields=${baseFields}&limit=14&page=${(dmPage % 2) + 1}&created_after=${days60}&sort=relevance&search=${encodeURIComponent(allTopics[idxA])}`,
          `/videos?fields=${baseFields}&limit=14&created_after=${days60}&sort=relevance&search=${encodeURIComponent(allTopics[idxB])}`,
          `/videos?fields=${baseFields}&limit=12&created_after=${days60}&sort=relevance&search=${encodeURIComponent(allTopics[idxC])}`,
        ];
      }
    }
  }

  switch (category) {
    case 'tech':
      return [
        `/videos?fields=${baseFields}&limit=18&page=${dmPage}&channel=tech&created_after=${days60}&sort=visited-month`,
        `/videos?fields=${baseFields}&limit=14&created_after=${days60}&sort=relevance&search=${encodeURIComponent('smartphone ai review 2026')}`,
      ];
    case 'music':
      return [
        `/videos?fields=${baseFields}&limit=18&page=${dmPage}&channel=music&created_after=${days60}&sort=visited-month`,
        `/videos?fields=${baseFields}&limit=14&created_after=${days60}&sort=relevance&search=${encodeURIComponent('official music video 2026')}`,
      ];
    case 'gaming':
      return [
        `/videos?fields=${baseFields}&limit=18&page=${dmPage}&channel=videogames&created_after=${days60}&sort=visited-month`,
        `/videos?fields=${baseFields}&limit=14&created_after=${days60}&sort=relevance&search=${encodeURIComponent('gameplay review 2026')}`,
      ];
    case 'education':
      return [
        `/videos?fields=${baseFields}&limit=18&page=${dmPage}&channel=school&created_after=${days60}&sort=visited-month`,
        `/videos?fields=${baseFields}&limit=14&created_after=${days60}&sort=relevance&search=${encodeURIComponent('science documentary 2026')}`,
      ];
    case 'news':
      return [
        `/videos?fields=${baseFields}&limit=18&page=${dmPage}&channel=news${langParam}&created_after=${days60}&sort=recent`,
        `/videos?fields=${baseFields}&limit=14&channel=news&created_after=${days60}&sort=visited-week`,
      ];
    case 'all':
    default:
      return [
        `/videos?fields=${baseFields}&limit=16&page=${dmPage}${langParam}&created_after=${days14}&sort=recent`,
        `/videos?fields=${baseFields}&limit=16&page=${dmPage}${langParam}&created_after=${days60}&sort=visited-week`,
        `/videos?fields=${baseFields}&limit=14&channel=shortfilms&created_after=${days60}&sort=visited-month`,
        `/videos?fields=${baseFields}&limit=14&channel=news&created_after=${days60}&sort=recent`,
      ];
  }
}

export async function getTrendingMediaVideos(
  category: TrendingCategory = 'all',
  hl: AppLocale = 'ar',
  options?: { refresh?: boolean; seed?: number },
): Promise<TrendingResponse> {
  const ytPlayable = await canUseYouTubeStreams(hl);
  const refresh = Boolean(options?.refresh);
  const cacheKey = `feed:trending:${ytPlayable ? 'yt' : 'dm'}:${category}:${hl}`;

  if (!refresh) {
    const cached = getCached<TrendingResponse>(cacheKey);
    if (cached) return cached;
  }

  trendingRotationCounter += 1;
  const activeSeed =
    typeof options?.seed === 'number' && Number.isFinite(options.seed)
      ? Math.abs(Math.floor(options.seed))
      : trendingRotationCounter;

  let items: MediaVideo[] = [];

  if (ytPlayable) {
    const queryConfigs = (YT_TRENDING_QUERIES[category] || YT_TRENDING_QUERIES.all)[hl];
    const batches = await runWithCatalogClient(
      hl,
      async (yt) =>
        Promise.all(
          queryConfigs.map(async (cfg) => {
            try {
              const res = await yt.search(cfg.q, {
                type: 'video',
                upload_date: cfg.upload_date || 'week',
              });
              const parsedItems: MediaVideo[] = [];
              for (const rawNode of res.videos || []) {
                const parsed = parseYouTubeVideoNode(rawNode, hl);
                if (parsed) parsedItems.push(parsed);
              }
              return parsedItems;
            } catch {
              return [];
            }
          }),
        ),
      (res) => res.every((b) => b.length === 0),
    ).catch(() => [] as MediaVideo[][]);

    const limit = category === 'all' ? 60 : 48;
    const rotated = refresh ? rotateFreshBatches(batches, activeSeed) : batches;
    items = interleaveMediaVideos(rotated, limit);
  }

  // Default cloud path (or fallback if YouTube returned empty): 100% playable fresh Dailymotion catalog
  if (items.length === 0) {
    const paths = buildFreshPlayableTrendingPaths(category, hl, activeSeed);
    const rawBatches = await Promise.all(
      paths.map((path) =>
        fetchDailymotionJson<{ list?: RawDailymotionVideo[] }>(path)
          .then((r) => filterCleanRawVideos(r.list || []))
          .catch(() => [] as RawDailymotionVideo[]),
      ),
    );
    const rotatedRawBatches = rotateFreshBatches(rawBatches, activeSeed);
    const prioritized = prioritizeFreshRawVideos(rotatedRawBatches, {
      maxAgeDays: 90,
      strictFresh: true,
      limit: category === 'all' ? 60 : 48,
    });

    // Fast parallel metadata check on top 16 entries so deleted/410 index items never appear at top of feed
    const headRaw = prioritized.slice(0, 16);
    const tailRaw = prioritized.slice(16);
    const verifiedHeadFlags = await Promise.all(
      headRaw.map((raw) =>
        fetchDailymotionMasterInfo(String(raw.id || ''))
          .then((info) => Boolean(info?.masterUrl))
          .catch(() => false),
      ),
    );
    const verifiedList = [
      ...headRaw.filter((_raw, idx) => verifiedHeadFlags[idx]),
      ...tailRaw,
    ];

    for (const raw of verifiedList) {
      const parsed = parseMediaVideo(raw, hl);
      if (parsed) items.push(parsed);
    }
  }

  const payload: TrendingResponse = {
    category,
    items,
    source: 'media-server',
    hl,
  };
  if (items.length > 0) {
    setCached(cacheKey, payload, 60 * 1000);
  }
  return payload;
}

function storeSearchContinuation(searchObj: unknown): string | null {
  if (!searchObj || !(searchObj as { has_continuation?: boolean }).has_continuation) {
    return null;
  }
  if (searchContinuationStore.size > 120) {
    const oldestKey = searchContinuationStore.keys().next().value;
    if (oldestKey) searchContinuationStore.delete(oldestKey);
  }
  const token = `ytc_${Date.now().toString(36)}_${Math.random().toString(36).slice(2, 8)}`;
  searchContinuationStore.set(token, {
    searchObj,
    expiresAt: Date.now() + 15 * 60 * 1000,
  });
  return token;
}

function mapDmSort(sort: SortOrder): string {
  switch (sort) {
    case 'date':
      return 'recent';
    case 'views':
      return 'visited-month';
    case 'rating':
      return 'visited';
    case 'relevance':
    default:
      return 'relevance';
  }
}

function buildDmDurationQuery(duration: DurationFilter, type: SearchType): string {
  if (type === 'short' || duration === 'short') return '&shorter_than=4';
  if (duration === 'medium') return '&longer_than=4&shorter_than=20';
  if (duration === 'long') return '&longer_than=20';
  return '';
}

export async function searchMediaVideos(params: {
  query: string;
  sort?: SortOrder;
  type?: SearchType;
  duration?: DurationFilter;
  continuation?: string;
  hl?: AppLocale;
}): Promise<SearchResponse> {
  const query = params.query.trim();
  const sort: SortOrder = params.sort || 'relevance';
  const type: SearchType = params.type || 'all';
  const duration: DurationFilter = params.duration || 'any';
  const hl: AppLocale = params.hl === 'en' ? 'en' : 'ar';

  if (params.continuation) {
    if (params.continuation.startsWith('dm_page:')) {
      const nextPage = Number.parseInt(params.continuation.slice('dm_page:'.length), 10) || 2;
      const baseFields = encodeURIComponent(DM_VIDEO_FIELDS);
      const durQ = buildDmDurationQuery(duration, type);
      const dmSort = mapDmSort(sort);
      const liveQ = type === 'live' ? '&flags=live_onair' : '';
      const more = await fetchDailymotionJson<{ list?: RawDailymotionVideo[]; has_more?: boolean }>(
        `/videos?fields=${baseFields}&limit=24&page=${nextPage}&sort=${dmSort}${durQ}${liveQ}&search=${encodeURIComponent(query)}`,
      ).catch(() => ({ list: [], has_more: false }));

      const items = filterCleanRawVideos(more.list || [])
        .map((r) => parseMediaVideo(r, hl))
        .filter((v): v is MediaVideo => Boolean(v));
      return {
        query,
        sort,
        type,
        duration,
        estimatedResults: items.length,
        items,
        channels: [],
        continuation: more.has_more ? `dm_page:${nextPage + 1}` : null,
        source: 'media-server',
        hl,
      };
    }

    if (searchContinuationStore.has(params.continuation)) {
      const stored = searchContinuationStore.get(params.continuation);
      if (stored && stored.expiresAt > Date.now() && typeof stored.searchObj?.getContinuation === 'function') {
        const nextSearch = await stored.searchObj.getContinuation();
        const items: MediaVideo[] = [];
        for (const rawNode of nextSearch.videos || []) {
          const parsed = parseYouTubeVideoNode(rawNode, hl);
          if (parsed) items.push(parsed);
        }
        return {
          query,
          sort,
          type,
          duration,
          estimatedResults: items.length,
          items,
          channels: [],
          continuation: storeSearchContinuation(nextSearch),
          source: 'media-server',
          hl,
        };
      }
    }
  }

  const cacheKey = `search:yt:${query}:${sort}:${type}:${duration}:${hl}`;
  const cached = getCached<SearchResponse>(cacheKey);
  if (cached) return cached;

  const channelMap = new Map<string, MediaChannelSummary>();
  const videoMap = new Map<string, MediaVideo>();
  let continuation: string | null = null;
  let estimatedResults = 0;

  // Helper to fetch YouTube channels safely with cookie-free Innertube session recovery
  const fetchYouTubeChannels = async (): Promise<MediaChannelSummary[]> => {
    const parsed: MediaChannelSummary[] = [];
    const seen = new Set<string>();
    const addNode = (node: unknown) => {
      const ch = parseYouTubeChannelSummary(node);
      if (ch && !seen.has(ch.id)) {
        seen.add(ch.id);
        parsed.push(ch);
      }
    };

    try {
      const chRes = await runWithCatalogClient(
        hl,
        (yt) => yt.search(query, { type: 'channel' }),
        (res) => (res.channels?.length || 0) === 0 && (res.results?.length || 0) === 0,
      );
      for (const chNode of chRes.channels || []) addNode(chNode);
      for (const rNode of chRes.results || []) {
        if ((rNode as { type?: string })?.type === 'Channel') addNode(rNode);
      }
    } catch {
      // Fallback below
    }

    // If stripped/normalized Arabic query differs, check normalized too
    if (parsed.length === 0) {
      const normQ = normalizeGlobalQuery(query);
      if (normQ && normQ !== query) {
        try {
          const chRes2 = await runWithCatalogClient(hl, (yt) => yt.search(normQ, { type: 'channel' }));
          for (const chNode of chRes2.channels || []) addNode(chNode);
        } catch {
          // ignore
        }
      }
    }
    return parsed;
  };

  // Primary: Real YouTube Search API for matching channels and up-to-date videos
  const searchFilters: NonNullable<Parameters<Innertube['search']>[1]> = {};
  if (sort === 'views' || sort === 'rating') {
    searchFilters.prioritize = 'popularity';
  } else if (sort === 'date') {
    searchFilters.upload_date = 'month';
    searchFilters.type = 'video';
  } else {
    searchFilters.prioritize = 'relevance';
  }

  if (type === 'live') {
    searchFilters.type = 'video';
    searchFilters.features = ['live'];
  } else if (type === 'short') {
    searchFilters.type = 'video';
    searchFilters.duration = 'under_three_mins';
  } else if (type === 'video') {
    searchFilters.type = 'video';
  } else if (!searchFilters.type) {
    searchFilters.type = 'all';
  }

  if (duration === 'short') {
    searchFilters.type = 'video';
    searchFilters.duration = 'under_three_mins';
  } else if (duration === 'medium') {
    searchFilters.type = 'video';
    searchFilters.duration = 'three_to_twenty_mins';
  } else if (duration === 'long') {
    searchFilters.type = 'video';
    searchFilters.duration = 'over_twenty_mins';
  }

  const [mainSearch, ytChannels] = await Promise.all([
    runWithCatalogClient(
      hl,
      (yt) => yt.search(query, searchFilters),
      (res) => (res.videos?.length || 0) === 0 && (res.channels?.length || 0) === 0,
    ).catch(() => null),
    type === 'all' && query ? fetchYouTubeChannels() : Promise.resolve([]),
  ]);

  const mainChs: MediaChannelSummary[] = [];
  for (const chNode of mainSearch?.channels || []) {
    const parsedCh = parseYouTubeChannelSummary(chNode);
    if (parsedCh) mainChs.push(parsedCh);
  }
  for (const ch of rankSearchChannels(query, [...ytChannels, ...mainChs], [], 12)) {
    channelMap.set(ch.id, ch);
  }
  for (const vNode of mainSearch?.videos || []) {
    const parsedV = parseYouTubeVideoNode(vNode, hl);
    if (parsedV && !videoMap.has(parsedV.id)) {
      videoMap.set(parsedV.id, parsedV);
    }
  }
  continuation = storeSearchContinuation(mainSearch);
  estimatedResults = Number(mainSearch?.estimated_results || 0);

  // Emergency fallback only if YouTube search returned zero videos
  if (videoMap.size === 0) {
    const baseFields = encodeURIComponent(DM_VIDEO_FIELDS);
    const durQ = buildDmDurationQuery(duration, type);
    const dmSort = mapDmSort(sort);
    const liveQ = type === 'live' ? '&flags=live_onair' : '';
    const days365 = Math.floor(Date.now() / 1000) - 365 * 86400;
    const normQuery = normalizeGlobalQuery(query);

    const [dmRelRes, dmFreshRes, dmUsersRes, ytChannels] = await Promise.all([
      fetchDailymotionJson<{ list?: RawDailymotionVideo[]; total?: number; has_more?: boolean }>(
        `/videos?fields=${baseFields}&limit=24&sort=${dmSort}${durQ}${liveQ}&search=${encodeURIComponent(query)}`,
      ).catch(() => ({ list: [], total: 0, has_more: false })),
      sort === 'relevance'
        ? fetchDailymotionJson<{ list?: RawDailymotionVideo[] }>(
            `/videos?fields=${baseFields}&limit=16&sort=relevance&created_after=${days365}${durQ}${liveQ}&search=${encodeURIComponent(normQuery || query)}`,
          ).catch(() => ({ list: [] }))
        : Promise.resolve({ list: [] }),
      type === 'all' && query
        ? fetchDailymotionJson<{ list?: RawDailymotionUser[] }>(
            `/users?fields=${encodeURIComponent(DM_USER_FIELDS)}&limit=10&search=${encodeURIComponent(query)}`,
          ).catch(() => ({ list: [] }))
        : Promise.resolve({ list: [] }),
      type === 'all' && query ? fetchYouTubeChannels() : Promise.resolve([]),
    ]);

    const dmChannels: MediaChannelSummary[] = [];
    for (const u of dmUsersRes.list || []) {
      const ch = parseMediaChannel(u, hl);
      if (ch) dmChannels.push(ch);
    }

    const rankedChannels = rankSearchChannels(query, ytChannels, dmChannels, 12);
    for (const ch of rankedChannels) {
      if (!channelMap.has(ch.id)) channelMap.set(ch.id, ch);
    }

    const batches: RawDailymotionVideo[][] = [
      filterCleanRawVideos(dmFreshRes.list || []),
      filterCleanRawVideos(dmRelRes.list || []),
    ];

    let mergedRaw = prioritizeFreshRawVideos(batches, {
      maxAgeDays: 540,
      strictFresh: false,
      limit: 30,
    });

    // Global Search Guarantee: broaden automatically with channel names + normalized tokens if exact phrase returned few videos
    if (mergedRaw.length < 6 && query) {
      const fallbacks = buildFallbackSearchQueries(query, hl);
      const channelHint = rankedChannels[0]?.name;
      const expandedQueries = channelHint ? [channelHint, ...fallbacks] : fallbacks;
      const extraBatches: RawDailymotionVideo[][] = [];
      for (const fbQuery of expandedQueries) {
        if (extraBatches.flat().length >= 20) break;
        const fbRes = await fetchDailymotionJson<{ list?: RawDailymotionVideo[] }>(
          `/videos?fields=${baseFields}&limit=14&sort=relevance${durQ}&search=${encodeURIComponent(fbQuery)}`,
        ).catch(() => ({ list: [] }));
        const cleanList = filterCleanRawVideos(fbRes.list || []);
        if (cleanList.length > 0) extraBatches.push(cleanList);
      }
      if (extraBatches.length > 0) {
        mergedRaw = prioritizeFreshRawVideos([mergedRaw, ...extraBatches], {
          maxAgeDays: 540,
          strictFresh: false,
          limit: 30,
        });
      }
    }

    for (const raw of mergedRaw) {
      const parsedV = parseMediaVideo(raw, hl);
      if (parsedV && !videoMap.has(parsedV.id)) {
        videoMap.set(parsedV.id, parsedV);
      }
    }

    if (!continuation && dmRelRes.has_more) {
      continuation = 'dm_page:2';
    }
    estimatedResults = Math.max(estimatedResults, Number(dmRelRes.total || 0), videoMap.size + channelMap.size);
  }

  const items = Array.from(videoMap.values());
  const channels = Array.from(channelMap.values());

  const response: SearchResponse = {
    query,
    sort,
    type,
    duration,
    estimatedResults: Math.max(estimatedResults, items.length + channels.length),
    items,
    channels,
    continuation,
    source: 'media-server',
    hl,
  };

  if (items.length > 0 || channels.length > 0) {
    setCached(cacheKey, response);
  }
  return response;
}

export async function getSuggestQueries(query: string, hl: AppLocale = 'ar'): Promise<SuggestResponse> {
  const clean = query.trim();
  if (!clean) {
    return { query: '', suggestions: [], source: 'media-suggest' };
  }

  const cacheKey = `yt:suggest:${clean}:${hl}`;
  const cached = getCached<SuggestResponse>(cacheKey);
  if (cached) return cached;

  try {
    const res = await fetch(
      `https://suggestqueries.google.com/complete/search?client=firefox&ds=yt&hl=${hl}&q=${encodeURIComponent(clean)}`,
      { headers: { 'User-Agent': DESKTOP_UA } },
    );
    if (!res.ok) throw new Error('Suggest failed');
    const json = (await res.json()) as [string, string[]];
    const suggestions = Array.isArray(json?.[1]) ? json[1].slice(0, 8) : [];
    const payload: SuggestResponse = {
      query: clean,
      suggestions,
      source: 'media-suggest',
    };
    setCached(cacheKey, payload, 10 * 60 * 1000);
    return payload;
  } catch {
    return {
      query: clean,
      suggestions: [],
      source: 'media-suggest',
    };
  }
}

function readUnknownText(val: unknown): string {
  if (!val) return '';
  if (typeof val === 'string') return val.trim();
  if (typeof val === 'object') {
    const obj = val as { text?: unknown; content?: unknown; toString?: () => string };
    if (typeof obj.text === 'string') return obj.text.trim();
    if (typeof obj.content === 'string') return obj.content.trim();
    if (typeof obj.toString === 'function') {
      const s = obj.toString();
      if (s && s !== '[object Object]') return s.trim();
    }
  }
  return '';
}

export async function getMediaVideoDetails(
  idOrUrl: string,
  hl: AppLocale = 'ar',
): Promise<VideoDetailsResponse | null> {
  const id = extractMediaId(idOrUrl);
  if (!id) return null;

  const cacheKey = `media:video:${id}:${hl}`;
  const cached = getCached<VideoDetailsResponse>(cacheKey);
  if (cached) return cached;

  // Support legacy Dailymotion IDs cleanly if user had saved/history items
  if (!isYouTubeVideoId(id)) {
    const [rawVideo, rawRelated] = await Promise.all([
      fetchDailymotionJson<RawDailymotionVideo>(
        `/video/${encodeURIComponent(id)}?fields=${encodeURIComponent(DM_VIDEO_FIELDS)}`,
      ),
      fetchDailymotionJson<{ list?: RawDailymotionVideo[] }>(
        `/video/${encodeURIComponent(id)}/related?fields=${encodeURIComponent(DM_VIDEO_FIELDS)}&limit=12`,
      ).catch(() => ({ list: [] })),
    ]);

    const base = parseMediaVideo(rawVideo, hl);
    if (!base) return null;

    const related: MediaVideo[] = [];
    for (const rel of rawRelated.list || []) {
      const parsedRel = parseMediaVideo(rel, hl);
      if (parsedRel && parsedRel.id !== base.id) related.push(parsedRel);
    }

    const likesCount = Number(rawVideo.likes_total || 0);
    const details: VideoDetailsResponse = {
      video: {
        ...base,
        description: stripHtmlTags(rawVideo.description) || base.title,
        subscribersText: formatSubscribersText(rawVideo['owner.followers_total'], hl),
        likesText: likesCount > 0 ? likesCount.toLocaleString() : undefined,
        uploadDateText: base.publishedText,
      },
      related,
      source: 'media-server',
    };
    setCached(cacheKey, details);
    return details;
  }

  const [info, commentsPage] = await Promise.all([
    runWithCatalogClient(hl, (yt) => yt.getInfo(id)),
    runWithCatalogClient(hl, (yt) => yt.getComments(id)).catch(() => null),
  ]);

  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  const pInfo = info.primary_info as any;
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  const sInfo = info.secondary_info as any;
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  const bInfo = info.basic_info as any;

  const title = readUnknownText(pInfo?.title) || String(bInfo?.title || '').trim() || id;
  const channelName =
    String(sInfo?.owner?.author?.name || bInfo?.author || '').trim() ||
    (hl === 'ar' ? 'مربع الدراما' : 'Drama Square');
  const channelId = String(sInfo?.owner?.author?.id || bInfo?.channel_id || '').trim();
  const channelAvatar = pickBestThumbnail(sInfo?.owner?.author?.thumbnails);
  const channelVerified = Boolean(sInfo?.owner?.author?.is_verified || sInfo?.owner?.author?.is_verified_artist);
  const subscribersText = readUnknownText(sInfo?.owner?.subscriber_count);
  const description = readUnknownText(sInfo?.description) || readUnknownText(bInfo?.short_description) || title;

  const viewsText =
    readUnknownText(pInfo?.view_count?.view_count) ||
    readUnknownText(pInfo?.view_count?.short_view_count) ||
    (typeof bInfo?.view_count === 'number'
      ? hl === 'ar'
        ? `${bInfo.view_count.toLocaleString()} مشاهدة`
        : `${bInfo.view_count.toLocaleString()} views`
      : '');
  const publishedText = readUnknownText(pInfo?.published);

  // Extract likes from primary_info menu buttons or basic_info
  let likesNum = typeof bInfo?.like_count === 'number' ? bInfo.like_count : 0;
  const topButtons = Array.isArray(pInfo?.menu?.top_level_buttons) ? pInfo.menu.top_level_buttons : [];
  for (const btn of topButtons) {
    if (typeof btn?.like_count === 'number' && btn.like_count > 0) {
      likesNum = btn.like_count;
      break;
    }
  }

  const durationSeconds = typeof bInfo?.duration === 'number' && bInfo.duration > 0 ? Math.floor(bInfo.duration) : 0;
  const isLive = Boolean(bInfo?.is_live);
  const thumbnail = pickBestThumbnail(bInfo?.thumbnail, id);

  let related: MediaVideo[] = [];
  const seenRel = new Set<string>([id]);
  for (const relNode of info.watch_next_feed || []) {
    const parsedRel = parseYouTubeVideoNode(relNode, hl);
    if (parsedRel && !seenRel.has(parsedRel.id)) {
      seenRel.add(parsedRel.id);
      related.push(parsedRel);
      if (related.length >= 16) break;
    }
  }

  if (related.length === 0) {
    const topicQuery = title.split(/[|/\-–—]/)[0]?.trim() || title.slice(0, 60);
    const dmRel = await fetchDailymotionJson<{ list?: RawDailymotionVideo[] }>(
      `/videos?fields=${encodeURIComponent(DM_VIDEO_FIELDS)}&limit=14&sort=relevance&search=${encodeURIComponent(topicQuery)}`,
      5000,
    ).catch(() => ({ list: [] }));
    related = filterCleanRawVideos(dmRel.list || [])
      .map((r) => parseMediaVideo(r, hl))
      .filter((v): v is MediaVideo => Boolean(v && v.id !== id))
      .slice(0, 14);
  }

  const comments: MediaComment[] = [];
  if (commentsPage?.contents) {
    let idx = 0;
    for (const thread of commentsPage.contents) {
      const parsedC = parseYouTubeCommentNode(thread, idx);
      idx += 1;
      if (parsedC) {
        comments.push(parsedC);
        if (comments.length >= 30) break;
      }
    }
  }

  const details: VideoDetailsResponse = {
    video: {
      id,
      title,
      channelName,
      channelId,
      channelAvatar: channelAvatar || undefined,
      channelVerified,
      thumbnail,
      duration: isLive ? (hl === 'ar' ? 'مباشر' : 'LIVE') : durationSeconds > 0 ? formatDurationSimple(durationSeconds) : '0:00',
      durationSeconds,
      isLive,
      isShort: durationSeconds > 0 && durationSeconds <= 60,
      viewsText,
      viewsCount: typeof bInfo?.view_count === 'number' ? bInfo.view_count : null,
      publishedText,
      descriptionSnippet: description.slice(0, 160),
      streamUrl: `/api/videos/item/${encodeURIComponent(id)}/stream.m3u8`,
      sourceType: 'video',
      description,
      subscribersText: subscribersText || '',
      likesText: likesNum > 0 ? likesNum.toLocaleString() : undefined,
      uploadDateText: publishedText || undefined,
    },
    related,
    comments,
    source: 'media-server',
  };

  setCached(cacheKey, details);
  return details;
}

function formatDurationSimple(totalSeconds: number): string {
  const safe = Math.max(0, Math.floor(totalSeconds));
  const h = Math.floor(safe / 3600);
  const m = Math.floor((safe % 3600) / 60);
  const s = safe % 60;
  const pad = (n: number) => String(n).padStart(2, '0');
  return h > 0 ? `${h}:${pad(m)}:${pad(s)}` : `${m}:${pad(s)}`;
}

export async function getMediaChannelDetails(
  channelId: string,
  hl: AppLocale = 'ar',
): Promise<ChannelResponse | null> {
  const cleanId = channelId.trim();
  if (!cleanId) return null;

  const cacheKey = `media:channel:yt:${cleanId}:${hl}`;
  const cached = getCached<ChannelResponse>(cacheKey);
  if (cached) return cached;

  // Handle YouTube UC... channels or @handles: fetch authentic channel feed directly
  if (cleanId.startsWith('UC') || cleanId.startsWith('@')) {
    const { ch, videosTab, liveTab } = await runWithCatalogClient(
      hl,
      async (yt) => {
        const channelObj = await yt.getChannel(cleanId);
        const vTab = await channelObj.getVideos().catch(() => null);
        const lTab =
          !vTab?.videos?.length && !channelObj.videos?.length
            ? await channelObj.getLiveStreams().catch(() => null)
            : null;
        return { ch: channelObj, videosTab: vTab, liveTab: lTab };
      },
      (res) =>
        !(res.videosTab?.videos?.length || res.ch.videos?.length || res.liveTab?.videos?.length),
    );

    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    const meta = ch.metadata as any;
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    const header = ch.header as any;

    const canonicalChannelId = String(meta?.external_id || cleanId);
    const name = String(meta?.title || cleanId).trim();
    const avatar = pickBestThumbnail(meta?.avatar);
    const banner =
      pickBestThumbnail(header?.content?.banner?.image) ||
      pickBestThumbnail(header?.banner);

    let subscribersText = '';
    const rows = header?.content?.metadata?.metadata_rows || [];
    for (const row of rows) {
      for (const part of row?.metadata_parts || []) {
        const txt = readUnknownText(part?.text ?? part);
        if (/مشترك|subscriber/i.test(txt)) {
          subscribersText = txt;
          break;
        }
      }
      if (subscribersText) break;
    }

    const videos: MediaVideo[] = [];
    const rawNodes = [
      ...(videosTab?.videos || []),
      ...(ch.videos || []),
      ...(liveTab?.videos || []),
    ];
    const seenIds = new Set<string>();
    for (const rawNode of rawNodes) {
      const parsed = parseYouTubeVideoNode(rawNode, hl);
      if (parsed && !seenIds.has(parsed.id)) {
        seenIds.add(parsed.id);
        videos.push({
          ...parsed,
          channelId: canonicalChannelId,
          channelName: name,
          channelAvatar: avatar || parsed.channelAvatar,
        });
      }
    }

    const payload: ChannelResponse = {
      channel: {
        id: canonicalChannelId,
        name,
        avatar: avatar || undefined,
        banner: banner || undefined,
        subscribersText: subscribersText || undefined,
        description: String(meta?.description || '').trim() || undefined,
      },
      videos,
      source: 'media-server',
    };
    if (videos.length > 0) {
      setCached(cacheKey, payload);
    }
    return payload;
  }

  // Fallback for legacy Dailymotion channel IDs
  const [rawUser, rawVideos] = await Promise.all([
    fetchDailymotionJson<RawDailymotionUser>(
      `/user/${encodeURIComponent(cleanId)}?fields=${encodeURIComponent(DM_USER_FIELDS)}`,
    ),
    fetchDailymotionJson<{ list?: RawDailymotionVideo[] }>(
      `/user/${encodeURIComponent(cleanId)}/videos?fields=${encodeURIComponent(DM_VIDEO_FIELDS)}&sort=recent&limit=24`,
    ).catch(() => ({ list: [] })),
  ]);

  const channel = parseMediaChannel(rawUser, hl);
  if (!channel) return null;

  const videos: MediaVideo[] = [];
  for (const raw of rawVideos.list || []) {
    const parsed = parseMediaVideo(raw, hl);
    if (parsed) {
      videos.push({
        ...parsed,
        channelName: parsed.channelName || channel.name,
        channelId: cleanId,
      });
    }
  }

  const payload: ChannelResponse = {
    channel: {
      ...channel,
      banner: rawUser.cover_250_url || undefined,
    },
    videos,
    source: 'media-server',
  };

  setCached(cacheKey, payload);
  return payload;
}

async function tryResolveDirectYouTubeStream(
  id: string,
  hl: AppLocale,
): Promise<{ kind: 'mp4' | 'hls'; upstreamUrl: string; title?: string } | null> {
  try {
    const ytPlayer = await getYoutubePlayerClient(hl);
    for (const clientType of ['WEB', 'TV', 'ANDROID_VR'] as const) {
      try {
        const info = await ytPlayer.getBasicInfo(id, { client: clientType });
        if (info.playability_status?.status !== 'OK') continue;

        const hls = info.streaming_data?.hls_manifest_url;
        if (hls) {
          return {
            kind: 'hls',
            upstreamUrl: hls,
            title: info.basic_info?.title,
          };
        }

        const muxedFormats = [...(info.streaming_data?.formats || [])]
          .filter((f) => f.has_video && f.has_audio)
          .sort((a, b) => (b.height || 0) - (a.height || 0));

        for (const fmt of muxedFormats) {
          try {
            const url = await fmt.decipher(ytPlayer.session.player);
            if (url) {
              return {
                kind: 'mp4',
                upstreamUrl: url,
                title: info.basic_info?.title,
              };
            }
          } catch {
            if (fmt.url) {
              return {
                kind: 'mp4',
                upstreamUrl: fmt.url,
                title: info.basic_info?.title,
              };
            }
          }
        }
      } catch {
        // try next clientType
      }
    }
  } catch {
    // Continue to ANDROID_VR attempt
  }

  // Secondary direct check with ANDROID_VR client (works without signature decipher for unblocked streams)
  try {
    const pr = await fetch('https://www.youtube.com/youtubei/v1/player?prettyPrint=false', {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'User-Agent': VR_UA,
      },
      body: JSON.stringify({
        context: {
          client: {
            clientName: 'ANDROID_VR',
            clientVersion: '1.60.19',
            deviceMake: 'Oculus',
            deviceModel: 'Quest 3',
            androidSdkVersion: 32,
            osName: 'Android',
            osVersion: '12L',
            hl,
            gl: getRegionForLocale(hl),
          },
        },
        videoId: id,
        contentCheckOk: true,
        racyOk: true,
      }),
    });

    if (pr.ok) {
      const pj = (await pr.json()) as {
        playabilityStatus?: { status?: string };
        videoDetails?: { title?: string };
        streamingData?: {
          hlsManifestUrl?: string;
          formats?: Array<{ url?: string; mimeType?: string; height?: number }>;
        };
      };
      if (pj.playabilityStatus?.status === 'OK') {
        if (pj.streamingData?.hlsManifestUrl) {
          return {
            kind: 'hls',
            upstreamUrl: pj.streamingData.hlsManifestUrl,
            title: pj.videoDetails?.title,
          };
        }
        const mp4 = (pj.streamingData?.formats || [])
          .filter((f) => Boolean(f.url) && (f.mimeType || '').includes('video/mp4'))
          .sort((a, b) => (b.height || 0) - (a.height || 0))[0];
        if (mp4?.url) {
          return {
            kind: 'mp4',
            upstreamUrl: mp4.url,
            title: pj.videoDetails?.title,
          };
        }
      }
    }
  } catch {
    // fallback handled by caller
  }

  return null;
}

const verifiedLiveHosts = new Set<string>();

function registerVerifiedHost(rawUrl: string): void {
  try {
    const parsed = new URL(rawUrl);
    if (parsed.protocol !== 'http:' && parsed.protocol !== 'https:') return;
    const host = parsed.hostname.toLowerCase();
    if (!host) return;
    if (verifiedLiveHosts.size > 500) {
      verifiedLiveHosts.clear();
    }
    verifiedLiveHosts.add(host);
  } catch {
    // ignore invalid URL
  }
}

function registerManifestChildHosts(manifestText: string, baseUrl: string): void {
  for (const rawLine of manifestText.split(/\r?\n/)) {
    const line = rawLine.trim();
    if (!line) continue;
    if (line.startsWith('#')) {
      const matches = line.matchAll(/URI="([^"]+)"/g);
      for (const m of matches) {
        try {
          registerVerifiedHost(new URL(m[1], baseUrl).toString());
        } catch {
          // ignore
        }
      }
      continue;
    }
    try {
      registerVerifiedHost(new URL(line, baseUrl).toString());
    } catch {
      // ignore
    }
  }
}

function isVerifiedLiveHost(targetUrl: string): boolean {
  try {
    const parsed = new URL(targetUrl);
    if (parsed.protocol !== 'http:' && parsed.protocol !== 'https:') return false;
    return verifiedLiveHosts.has(parsed.hostname.toLowerCase());
  } catch {
    return false;
  }
}

function resolveRefererForUrl(targetUrl: string): string | null {
  try {
    const host = new URL(targetUrl).hostname.toLowerCase();
    if (host === 'googlevideo.com' || host.endsWith('.googlevideo.com')) {
      return 'https://www.youtube.com/';
    }
    if (
      host === 'dmcdn.net' ||
      host.endsWith('.dmcdn.net') ||
      host === 'dailymotion.com' ||
      host.endsWith('.dailymotion.com') ||
      host === 'dm-event.net' ||
      host.endsWith('.dm-event.net')
    ) {
      return 'https://www.dailymotion.com/';
    }
  } catch {
    // ignore
  }
  return null;
}

async function getLiveDirectoryEntries(): Promise<LiveChannelEntry[]> {
  const cacheKey = 'feed:live-directory:v1';
  const cached = getCached<LiveChannelEntry[]>(cacheKey);
  if (cached) return cached;

  const sources = [
    'https://iptv-org.github.io/iptv/countries/iq.m3u',
    'https://iptv-org.github.io/iptv/languages/ara.m3u',
  ];

  const collected: LiveChannelEntry[] = [];
  await Promise.all(
    sources.map(async (src) => {
      const controller = new AbortController();
      const timer = setTimeout(() => controller.abort(), 3500);
      try {
        const res = await fetch(src, {
          headers: { 'User-Agent': DESKTOP_UA },
          signal: controller.signal,
        });
        if (res.ok) {
          const txt = await res.text();
          collected.push(...parseM3uLivePlaylist(txt));
        }
      } catch {
        // non-blocking fallback to built-in curated live directory
      } finally {
        clearTimeout(timer);
      }
    }),
  );

  setCached(cacheKey, collected, 30 * 60 * 1000);
  return collected;
}

async function canPlayHlsDirectly(targetUrl: string): Promise<boolean> {
  if (!targetUrl.startsWith('https://')) return false;
  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), 3500);
  try {
    const res = await fetch(targetUrl, {
      headers: {
        'User-Agent': DESKTOP_UA,
        Origin: 'http://localhost:3000',
        Accept: 'application/vnd.apple.mpegurl, */*',
      },
      signal: controller.signal,
    });
    const allowed = res.ok && Boolean(res.headers.get('access-control-allow-origin'));
    try {
      await res.body?.cancel();
    } catch {
      // ignore cancel errors
    }
    return allowed;
  } catch {
    return false;
  } finally {
    clearTimeout(timer);
  }
}

async function resolveLiveBroadcastStream(
  id: string,
  hl: AppLocale,
  titleHint?: string,
): Promise<{ kind: 'hls'; upstreamUrl: string; directCorsAllowed: boolean; title?: string } | null> {
  const cleanHint = (titleHint || '').trim();
  const dynamicEntries = await getLiveDirectoryEntries().catch(() => [] as LiveChannelEntry[]);

  let matched = cleanHint
    ? matchLiveBroadcastStream(cleanHint, '', false, dynamicEntries)
    : null;
  let resolvedTitle = cleanHint;

  if (!matched) {
    const details = await getMediaVideoDetails(id, hl).catch(() => null);
    if (details?.video) {
      resolvedTitle = details.video.title || cleanHint;
      matched = matchLiveBroadcastStream(
        details.video.title,
        details.video.channelName,
        Boolean(details.video.isLive),
        dynamicEntries,
      );
    }
  }

  if (!matched) return null;

  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), 4500);
  try {
    const probe = await fetch(matched.url, {
      headers: {
        'User-Agent': DESKTOP_UA,
        Origin: 'http://localhost:3000',
        Accept: 'application/vnd.apple.mpegurl, */*',
      },
      signal: controller.signal,
    });
    if (!probe.ok) return null;
    const finalUrl = probe.url || matched.url;
    const directCorsAllowed =
      finalUrl.startsWith('https://') &&
      Boolean(probe.headers.get('access-control-allow-origin'));
    registerVerifiedHost(matched.url);
    registerVerifiedHost(finalUrl);
    const preview = await probe.text().catch(() => '');
    if (preview) {
      registerManifestChildHosts(preview, finalUrl);
    }
    return {
      kind: 'hls',
      upstreamUrl: finalUrl,
      directCorsAllowed,
      title: resolvedTitle || matched.label,
    };
  } catch {
    return null;
  } finally {
    clearTimeout(timer);
  }
}

let ytDlpInstallPromise: Promise<string | null> | null = null;

async function ensureYtDlpBinary(): Promise<string | null> {
  const candidates = [
    process.env.YT_DLP_PATH?.trim() || '',
    '/tmp/yt-dlp',
    '/usr/local/bin/yt-dlp',
    '/usr/bin/yt-dlp',
  ].filter(Boolean);

  for (const binPath of candidates) {
    try {
      await fs.access(binPath, fs.constants.X_OK);
      return binPath;
    } catch {
      // check next path
    }
  }

  if (ytDlpInstallPromise) return ytDlpInstallPromise;

  ytDlpInstallPromise = (async () => {
    const targetPath = '/tmp/yt-dlp';
    const controller = new AbortController();
    const timer = setTimeout(() => controller.abort(), 15000);
    try {
      const res = await fetch(
        'https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp',
        { headers: { 'User-Agent': DESKTOP_UA }, signal: controller.signal },
      );
      if (!res.ok) return null;
      const buf = Buffer.from(await res.arrayBuffer());
      if (buf.length < 100_000) return null;
      await fs.writeFile(targetPath, buf);
      await fs.chmod(targetPath, 0o755);
      return targetPath;
    } catch {
      return null;
    } finally {
      clearTimeout(timer);
      ytDlpInstallPromise = null;
    }
  })();

  return ytDlpInstallPromise;
}

async function tryResolveViaYtDlp(
  id: string,
): Promise<{ kind: 'mp4' | 'hls'; upstreamUrl: string; title?: string } | null> {
  const binPath = await ensureYtDlpBinary();
  if (!binPath) return null;

  const args = [
    '--js-runtimes',
    'node',
    '--no-playlist',
    '--no-warnings',
    '--skip-download',
    '--extractor-args',
    'youtube:player_client=tv,ios,android_vr,mweb',
    '-J',
  ];

  let tempCookiePath: string | null = null;
  if (hasPlausibleYouTubeCookies()) {
    const rawCookies = process.env.YT_COOKIES?.trim() || '';
    if (rawCookies.startsWith('# Netscape')) {
      tempCookiePath = path.join(os.tmpdir(), `yt-cookies-${process.pid}.txt`);
      await fs.writeFile(tempCookiePath, rawCookies, 'utf8').catch(() => {});
      args.push('--cookies', tempCookiePath);
    } else {
      args.push('--add-header', `Cookie:${rawCookies}`);
    }
  }

  args.push(`https://www.youtube.com/watch?v=${id}`);

  try {
    const { stdout } = await execFileAsync(binPath, args, {
      timeout: 14000,
      maxBuffer: 8 * 1024 * 1024,
    });
    const parsed = JSON.parse(stdout) as {
      title?: string;
      is_live?: boolean;
      manifest_url?: string;
      url?: string;
      formats?: Array<{
        url?: string;
        manifest_url?: string;
        ext?: string;
        vcodec?: string;
        acodec?: string;
        height?: number;
        protocol?: string;
      }>;
    };

    if (parsed.is_live && parsed.manifest_url) {
      registerVerifiedHost(parsed.manifest_url);
      return {
        kind: 'hls',
        upstreamUrl: parsed.manifest_url,
        title: parsed.title,
      };
    }

    const formats = Array.isArray(parsed.formats) ? parsed.formats : [];
    const muxedMp4 = formats
      .filter(
        (f) =>
          Boolean(f.url) &&
          f.vcodec &&
          f.vcodec !== 'none' &&
          f.acodec &&
          f.acodec !== 'none' &&
          f.protocol !== 'm3u8_native' &&
          f.protocol !== 'm3u8',
      )
      .sort((a, b) => {
        const aMp4 = a.ext === 'mp4' ? 1 : 0;
        const bMp4 = b.ext === 'mp4' ? 1 : 0;
        if (aMp4 !== bMp4) return bMp4 - aMp4;
        return (b.height || 0) - (a.height || 0);
      })[0];

    if (muxedMp4?.url) {
      return {
        kind: 'mp4',
        upstreamUrl: muxedMp4.url,
        title: parsed.title,
      };
    }

    const hlsFormat = formats.find(
      (f) =>
        Boolean(f.manifest_url || f.url) &&
        (f.protocol === 'm3u8' || f.protocol === 'm3u8_native' || (f.url || '').includes('.m3u8')),
    );
    const hlsUrl = hlsFormat?.manifest_url || hlsFormat?.url || parsed.manifest_url;
    if (hlsUrl) {
      registerVerifiedHost(hlsUrl);
      return {
        kind: 'hls',
        upstreamUrl: hlsUrl,
        title: parsed.title,
      };
    }
  } catch {
    // yt-dlp couldn't bypass LOGIN_REQUIRED without cookies/proxy; fall through cleanly
  } finally {
    if (tempCookiePath) {
      await fs.unlink(tempCookiePath).catch(() => {});
    }
  }

  return null;
}

async function tryResolveIndependentMirror(
  id: string,
  hl: AppLocale,
  titleHint?: string,
  relaxed = false,
): Promise<{ dmId: string; title: string } | null> {
  let title = (titleHint || '').trim();
  let durationSeconds = 0;

  if (!title || !relaxed) {
    const details = await getMediaVideoDetails(id, hl).catch(() => null);
    if (details?.video?.title && details.video.title !== id) {
      title = details.video.title;
      durationSeconds = details.video.durationSeconds || 0;
    }
  }

  if (!title || title === id) return null;

  try {
    const cleanTopic = title
      .split(/[|/\-–—]/)[0]
      ?.trim()
      .slice(0, 75) || title.slice(0, 75);
    const dmRes = await fetchDailymotionJson<{ list?: RawDailymotionVideo[] }>(
      `/videos?fields=id,title,duration&limit=10&sort=relevance&search=${encodeURIComponent(relaxed ? cleanTopic : title.slice(0, 75))}`,
      6000,
    );
    const candidates: Array<{ id: string; score: number; title: string }> = [];
    for (const cand of filterCleanRawVideos(dmRes.list || [])) {
      const cid = String(cand.id || '').trim();
      const cTitle = String(cand.title || '').trim();
      const cDur = Number(cand.duration || 0);
      if (!cid || !cTitle || cid === id) continue;
      const score = scoreStreamCandidateMatch(title, durationSeconds, cTitle, cDur);
      if (score >= (relaxed ? 0.35 : 0.55)) {
        candidates.push({ id: cid, score, title: cTitle });
      }
    }

    candidates.sort((a, b) => b.score - a.score);
    for (const cand of candidates.slice(0, 4)) {
      const info = await fetchDailymotionMasterInfo(cand.id).catch(() => null);
      if (info?.masterUrl) {
        return { dmId: cand.id, title: cand.title || title };
      }
    }

    // Fallback search when relaxed (proxy retry) by broader query tokens
    if (relaxed) {
      const fallbackQueries = buildFallbackSearchQueries(cleanTopic, hl);
      for (const fbq of fallbackQueries.slice(0, 2)) {
        const fbRes = await fetchDailymotionJson<{ list?: RawDailymotionVideo[] }>(
          `/videos?fields=id,title,duration&limit=6&sort=relevance&search=${encodeURIComponent(fbq)}`,
          5000,
        ).catch(() => ({ list: [] }));
        for (const cand of filterCleanRawVideos(fbRes.list || [])) {
          const cid = String(cand.id || '').trim();
          if (!cid || cid === id) continue;
          const info = await fetchDailymotionMasterInfo(cid).catch(() => null);
          if (info?.masterUrl) {
            return { dmId: cid, title: String(cand.title || title).trim() };
          }
        }
      }
    }
  } catch {
    // ignore mirror error
  }

  return null;
}

export async function resolveVideoPlayback(
  idOrUrl: string,
  hl: AppLocale = 'ar',
  options?: { titleHint?: string },
): Promise<StreamResolutionResult> {
  const cleanId = extractMediaId(idOrUrl);
  const titleHint = (options?.titleHint || '').trim();

  if (!cleanId) {
    return {
      playable: false,
      code: 'INVALID_ID',
      reason: hl === 'ar' ? 'معرّف الفيديو غير صالح' : 'Invalid video ID',
    };
  }

  if (!isYouTubeVideoId(cleanId)) {
    const dmInfo = await fetchDailymotionMasterInfo(cleanId).catch(() => null);
    if (dmInfo?.masterUrl) {
      const directAllowed = await canPlayHlsDirectly(dmInfo.masterUrl);
      return {
        playable: true,
        kind: 'hls',
        url: directAllowed
          ? dmInfo.masterUrl
          : `/api/videos/item/${encodeURIComponent(cleanId)}/stream.m3u8`,
        upstreamUrl: dmInfo.masterUrl,
        dmId: cleanId,
        title: dmInfo.title,
      };
    }

    return {
      playable: false,
      code: 'STREAM_UNAVAILABLE',
      reason:
        hl === 'ar'
          ? 'هذا الفيديو غير متاح للبث حالياً من المصدر.'
          : 'This video stream is currently unavailable from source.',
    };
  }

  const cacheKey = `ytstream:direct:${cleanId}`;
  const cached = getCached<StreamResolutionResult>(cacheKey);
  if (cached) return cached;

  const liveStream = await resolveLiveBroadcastStream(cleanId, hl, titleHint);
  if (liveStream) {
    const resolved: StreamResolutionResult = {
      playable: true,
      kind: 'hls',
      url: liveStream.directCorsAllowed
        ? liveStream.upstreamUrl
        : `/api/videos/item/${encodeURIComponent(cleanId)}/stream.m3u8`,
      upstreamUrl: liveStream.upstreamUrl,
      title: liveStream.title || titleHint,
    };
    setCached(cacheKey, resolved, 15 * 60 * 1000);
    return resolved;
  }

  const direct = await tryResolveDirectYouTubeStream(cleanId, hl);
  if (direct) {
    registerVerifiedHost(direct.upstreamUrl);
    const directUrl =
      direct.kind === 'mp4'
        ? direct.upstreamUrl
        : (await canPlayHlsDirectly(direct.upstreamUrl))
          ? direct.upstreamUrl
          : `/api/videos/item/${encodeURIComponent(cleanId)}/stream.m3u8`;
    const resolved: StreamResolutionResult = {
      playable: true,
      kind: direct.kind,
      url: directUrl,
      upstreamUrl: direct.upstreamUrl,
      title: direct.title,
    };
    setCached(cacheKey, resolved, 20 * 60 * 1000);
    return resolved;
  }

  const ytDlpResolved = await tryResolveViaYtDlp(cleanId);
  if (ytDlpResolved) {
    registerVerifiedHost(ytDlpResolved.upstreamUrl);
    const directUrl =
      ytDlpResolved.kind === 'mp4'
        ? ytDlpResolved.upstreamUrl
        : (await canPlayHlsDirectly(ytDlpResolved.upstreamUrl))
          ? ytDlpResolved.upstreamUrl
          : `/api/videos/item/${encodeURIComponent(cleanId)}/stream.m3u8`;
    const resolved: StreamResolutionResult = {
      playable: true,
      kind: ytDlpResolved.kind,
      url: directUrl,
      upstreamUrl: ytDlpResolved.upstreamUrl,
      title: ytDlpResolved.title || titleHint,
    };
    setCached(cacheKey, resolved, 20 * 60 * 1000);
    return resolved;
  }

  const mirror = await tryResolveIndependentMirror(cleanId, hl, titleHint, false);
  if (mirror) {
    const dmInfo = await fetchDailymotionMasterInfo(mirror.dmId).catch(() => null);
    const directAllowed = dmInfo?.masterUrl ? await canPlayHlsDirectly(dmInfo.masterUrl) : false;
    const resolved: StreamResolutionResult = {
      playable: true,
      kind: 'hls',
      url:
        directAllowed && dmInfo?.masterUrl
          ? dmInfo.masterUrl
          : `/api/videos/item/${encodeURIComponent(mirror.dmId)}/stream.m3u8`,
      upstreamUrl: dmInfo?.masterUrl,
      dmId: mirror.dmId,
      title: mirror.title,
    };
    setCached(cacheKey, resolved, 20 * 60 * 1000);
    return resolved;
  }

  const blocked: StreamResolutionResult = {
    playable: false,
    code: 'YT_STREAM_AUTH_REQUIRED',
    reason:
      hl === 'ar'
        ? 'هذا الفيديو محمي من المصدر الأصلي حالياً؛ جرب إعادة المحاولة أو تشغيل فيديو آخر.'
        : 'This video stream is currently restricted by the original source.',
  };
  setCached(cacheKey, blocked, 60 * 1000);
  return blocked;
}

async function fetchDailymotionMasterInfo(
  dmId: string,
): Promise<{ masterUrl: string; title?: string } | null> {
  const metaRes = await fetch(
    `https://www.dailymotion.com/player/metadata/video/${encodeURIComponent(dmId)}?embedder=https%3A%2F%2Fwww.dailymotion.com%2F`,
    {
      headers: {
        'User-Agent': DESKTOP_UA,
        Referer: 'https://www.dailymotion.com/',
        Origin: 'https://www.dailymotion.com',
      },
    },
  );
  if (!metaRes.ok) return null;

  const meta = (await metaRes.json()) as {
    title?: string;
    qualities?: Record<string, Array<{ type?: string; url?: string }>>;
  };
  const qualities = meta.qualities || {};
  const candidateList =
    qualities.auto ||
    qualities['1080'] ||
    qualities['720'] ||
    qualities['480'] ||
    qualities['380'] ||
    Object.values(qualities).flat();

  const masterUrl = candidateList.find((q) => q?.url)?.url;
  if (!masterUrl) return null;
  return { masterUrl, title: meta.title };
}

export async function streamVideoMasterManifest(id: string, res: Response): Promise<void> {
  const resolved = await resolveVideoPlayback(id, 'ar');
  if (!resolved.playable) {
    const errStatus =
      resolved.code === 'YT_STREAM_AUTH_REQUIRED'
        ? 403
        : resolved.code === 'STREAM_UNAVAILABLE'
          ? 404
          : 503;
    res.status(errStatus).json({ error: resolved.reason || 'Stream unavailable', code: resolved.code });
    return;
  }

  if (resolved.kind === 'hls' && resolved.upstreamUrl) {
    const headers: Record<string, string> = {
      'User-Agent': DESKTOP_UA,
      Accept: 'application/vnd.apple.mpegurl, */*',
    };
    const referer = resolveRefererForUrl(resolved.upstreamUrl);
    if (referer) headers.Referer = referer;

    const upstream = await fetch(resolved.upstreamUrl, { headers });
    if (!upstream.ok) {
      res.status(upstream.status || 502).json({ error: 'Failed to load HLS playlist' });
      return;
    }
    const finalManifestUrl = upstream.url || resolved.upstreamUrl;
    registerVerifiedHost(finalManifestUrl);
    const text = await upstream.text();
    registerManifestChildHosts(text, finalManifestUrl);
    const rewritten = rewriteM3u8Manifest(text, finalManifestUrl, '/api/videos/hls');
    res.status(200);
    res.setHeader('Content-Type', 'application/vnd.apple.mpegurl; charset=utf-8');
    res.setHeader('Cache-Control', 'no-cache');
    res.send(rewritten);
    return;
  }

  const dmId = resolved.dmId || (!isYouTubeVideoId(id) ? id : '');
  if (!dmId) {
    res.status(404).json({ error: 'HLS manifest unavailable for this video' });
    return;
  }

  const dmInfo = await fetchDailymotionMasterInfo(dmId);
  if (!dmInfo) {
    res.status(404).json({ error: 'Playable stream unavailable for this video' });
    return;
  }

  const masterRes = await fetch(dmInfo.masterUrl, {
    headers: {
      'User-Agent': DESKTOP_UA,
      Referer: 'https://www.dailymotion.com/',
    },
  });

  if (!masterRes.ok) {
    res.status(masterRes.status || 502).json({ error: 'Failed to fetch stream playlist' });
    return;
  }

  const manifestText = await masterRes.text();
  const rewritten = rewriteM3u8Manifest(manifestText, masterRes.url || dmInfo.masterUrl, '/api/videos/hls');

  res.status(200);
  res.setHeader('Content-Type', 'application/vnd.apple.mpegurl; charset=utf-8');
  res.setHeader('Cache-Control', 'no-cache');
  res.send(rewritten);
}

export async function streamDirectVideoMp4(
  id: string,
  req: Request,
  res: Response,
): Promise<void> {
  const resolved = await resolveVideoPlayback(id, 'ar');
  if (!resolved.playable || resolved.kind !== 'mp4' || !resolved.upstreamUrl) {
    res.status(503).json({ error: resolved.reason || 'Direct MP4 stream unavailable' });
    return;
  }

  const headers: Record<string, string> = {
    'User-Agent': DESKTOP_UA,
    Referer: 'https://www.youtube.com/',
  };
  if (typeof req.headers.range === 'string') {
    headers.Range = req.headers.range;
  }

  const upstream = await fetch(resolved.upstreamUrl, { headers });
  if (!upstream.ok && upstream.status !== 206) {
    res.status(upstream.status || 502).end();
    return;
  }

  res.status(upstream.status);
  res.setHeader('Content-Type', upstream.headers.get('content-type') || 'video/mp4');
  res.setHeader('Accept-Ranges', 'bytes');
  const len = upstream.headers.get('content-length');
  const range = upstream.headers.get('content-range');
  if (len) res.setHeader('Content-Length', len);
  if (range) res.setHeader('Content-Range', range);

  if (!upstream.body) {
    res.end();
    return;
  }

  const nodeStream = Readable.fromWeb(upstream.body as unknown as NodeReadableStream);
  nodeStream.on('error', () => {
    if (!res.headersSent) res.status(502);
    res.end();
  });
  nodeStream.pipe(res);
}

export async function proxyHlsResource(
  targetUrl: string,
  rangeHeader: string | undefined,
  res: Response,
): Promise<void> {
  if (!isAllowedStreamHost(targetUrl) && !isVerifiedLiveHost(targetUrl)) {
    res.status(403).json({ error: 'Forbidden stream host' });
    return;
  }

  const headers: Record<string, string> = {
    'User-Agent': DESKTOP_UA,
  };
  const referer = resolveRefererForUrl(targetUrl);
  if (referer) {
    headers.Referer = referer;
  }
  if (rangeHeader) {
    headers.Range = rangeHeader;
  }

  const upstream = await fetch(targetUrl, { headers });
  if (!upstream.ok && upstream.status !== 206) {
    res.status(upstream.status || 502).end();
    return;
  }

  if (upstream.url) {
    registerVerifiedHost(upstream.url);
  }

  const ct = upstream.headers.get('content-type') || '';
  const isPlaylist =
    targetUrl.includes('.m3u8') || ct.includes('mpegurl') || ct.includes('x-mpegurl');

  if (isPlaylist) {
    const finalManifestUrl = upstream.url || targetUrl;
    const text = await upstream.text();
    registerManifestChildHosts(text, finalManifestUrl);
    const rewritten = rewriteM3u8Manifest(text, finalManifestUrl, '/api/videos/hls');
    res.status(200);
    res.setHeader('Content-Type', 'application/vnd.apple.mpegurl; charset=utf-8');
    res.setHeader('Cache-Control', 'no-cache');
    res.send(rewritten);
    return;
  }

  res.status(upstream.status);
  if (ct) res.setHeader('Content-Type', ct);
  const contentLength = upstream.headers.get('content-length');
  const contentRange = upstream.headers.get('content-range');
  if (contentLength) res.setHeader('Content-Length', contentLength);
  if (contentRange) res.setHeader('Content-Range', contentRange);
  res.setHeader('Cache-Control', 'public, max-age=600');

  if (!upstream.body) {
    res.end();
    return;
  }

  const nodeStream = Readable.fromWeb(upstream.body as unknown as NodeReadableStream);
  nodeStream.on('error', () => {
    if (!res.headersSent) res.status(502);
    res.end();
  });
  nodeStream.pipe(res);
}

export async function downloadVideoAsMp4(
  id: string,
  req: Request,
  res: Response,
): Promise<void> {
  const cleanId = extractMediaId(id);
  if (!cleanId) {
    res.status(400).json({ error: 'Invalid video ID' });
    return;
  }

  const resolved = await resolveVideoPlayback(cleanId, 'ar');
  if (!resolved.playable) {
    res.status(503).json({
      error: resolved.reason || 'Download unavailable without YT_COOKIES',
      code: resolved.code,
    });
    return;
  }

  const filename = sanitizeDownloadFilename(resolved.title || '', cleanId);
  const asciiFallback = `dramasquare-${cleanId}.mp4`;

  // Direct progressive MP4 from YouTube -> stream directly with Content-Length
  if (resolved.kind === 'mp4' && resolved.upstreamUrl) {
    const upstream = await fetch(resolved.upstreamUrl, {
      headers: { 'User-Agent': DESKTOP_UA },
    });
    if (!upstream.ok || !upstream.body) {
      res.status(upstream.status || 502).json({ error: 'MP4 upstream stream unavailable' });
      return;
    }

    res.status(200);
    res.setHeader('Content-Type', 'video/mp4');
    res.setHeader(
      'Content-Disposition',
      `attachment; filename="${asciiFallback}"; filename*=UTF-8''${encodeURIComponent(filename)}`,
    );
    res.setHeader('Cache-Control', 'no-store');
    res.setHeader('Access-Control-Expose-Headers', 'Content-Disposition, Content-Length');
    const len = upstream.headers.get('content-length');
    if (len) res.setHeader('Content-Length', len);

    const nodeStream = Readable.fromWeb(upstream.body as unknown as NodeReadableStream);
    nodeStream.on('error', () => {
      if (!res.writableEnded) res.end();
    });
    nodeStream.pipe(res);
    return;
  }

  // HLS -> MP4 remux via FFmpeg
  let inputUrl = resolved.upstreamUrl || '';
  if (!inputUrl && resolved.dmId) {
    const dmInfo = await fetchDailymotionMasterInfo(resolved.dmId);
    if (!dmInfo) {
      res.status(404).json({ error: 'Downloadable stream unavailable' });
      return;
    }
    inputUrl = dmInfo.masterUrl;
    try {
      const masterRes = await fetch(dmInfo.masterUrl, {
        headers: {
          'User-Agent': DESKTOP_UA,
          Referer: 'https://www.dailymotion.com/',
        },
      });
      if (masterRes.ok) {
        const masterText = await masterRes.text();
        const picked = pickDownloadVariantUrl(masterText, masterRes.url || dmInfo.masterUrl, 480);
        if (picked) inputUrl = picked;
      }
    } catch {
      // keep masterUrl
    }
  }

  if (!inputUrl) {
    res.status(404).json({ error: 'Downloadable stream unavailable' });
    return;
  }

  res.status(200);
  res.setHeader('Content-Type', 'video/mp4');
  res.setHeader(
    'Content-Disposition',
    `attachment; filename="${asciiFallback}"; filename*=UTF-8''${encodeURIComponent(filename)}`,
  );
  res.setHeader('Cache-Control', 'no-store');
  res.setHeader('Access-Control-Expose-Headers', 'Content-Disposition, Content-Length');

  const ffmpegReferer = resolveRefererForUrl(inputUrl);
  const ffmpegHeaders = ffmpegReferer
    ? `Referer: ${ffmpegReferer}\r\nUser-Agent: ${DESKTOP_UA}\r\n`
    : `User-Agent: ${DESKTOP_UA}\r\n`;

  const ffmpeg = spawn('ffmpeg', [
    '-hide_banner',
    '-loglevel',
    'error',
    '-headers',
    ffmpegHeaders,
    '-i',
    inputUrl,
    '-c',
    'copy',
    '-bsf:a',
    'aac_adtstoasc',
    '-movflags',
    'frag_keyframe+empty_moov+default_base_moof',
    '-f',
    'mp4',
    'pipe:1',
  ]);

  let clientClosed = false;
  req.on('close', () => {
    clientClosed = true;
    if (!ffmpeg.killed) {
      ffmpeg.kill('SIGKILL');
    }
  });

  ffmpeg.stdout.pipe(res);

  ffmpeg.stderr.on('data', (chunk: Buffer) => {
    const msg = chunk.toString().trim();
    if (msg && !clientClosed) {
      console.error(`[downloadVideoAsMp4:${cleanId}]`, msg);
    }
  });

  ffmpeg.on('error', () => {
    if (!res.headersSent) {
      res.status(500).json({ error: 'FFmpeg remuxer failed to start' });
    } else if (!res.writableEnded) {
      res.end();
    }
  });

  ffmpeg.on('close', (code) => {
    if (code !== 0 && !res.headersSent) {
      res.status(502).json({ error: 'Failed to prepare MP4 download' });
    } else if (!res.writableEnded) {
      res.end();
    }
  });
}
