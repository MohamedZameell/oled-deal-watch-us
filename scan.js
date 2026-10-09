// OLED deal watch: scrape retailers, compare every listing against what OTHER sellers charge for the same
// model, re-open the product page to confirm price + stock, then email the anomalies.
// One engine for every region; config.json holds the region, sources and thresholds.
// Usage: node scan.js [--dry] [--verify-sample]
//   --dry            print the digest instead of sending it, and don't persist state
//   --verify-sample  also run the product-page check on the 3 cheapest listings (tests the verifier)
// Env: CONFIG, STATE_DIR, CDP_URL (drive an existing browser), BROWSER_CHANNEL (e.g. chrome),
//      MAIL_VIA_GH (relay mail through that repo's mail.yml), FORCE_EMAIL, DEBUG_ITEMS
import { chromium } from 'playwright';
import nodemailer from 'nodemailer';
import fs from 'node:fs';
import path from 'node:path';

const DRY = process.argv.includes('--dry');
const VERIFY_SAMPLE = process.argv.includes('--verify-sample');
const cfg = JSON.parse(fs.readFileSync(process.env.CONFIG || 'config.json', 'utf8'));
const R = cfg.region;
const STATE = process.env.STATE_DIR || 'state';
fs.mkdirSync(STATE, { recursive: true });
const readJsonAt = (p, d) => { try { return JSON.parse(fs.readFileSync(p, 'utf8')); } catch { return d; } };
const readJson = (f, d) => readJsonAt(`${STATE}/${f}`, d);
const writeJson = (f, v) => { if (!DRY) fs.writeFileSync(`${STATE}/${f}`, JSON.stringify(v, null, 1)); };
const HOUR = 3600e3; const DAY = 24 * HOUR;

const MONITOR_OK = /monitor|odyssey|ultragear|alienware|aorus|\brog\b|mpg|mag\s?\d|agon|legion|evnia|mobiuz|xeneon|viewfinity|predator|nitro|xg\d{4}|\bAW\d{4}/i;
const NOT_MONITOR = /watch|laptop|notebook|\btv\b|television|smartphone|phone|zenbook|ideapad|vivobook|cooler|ryujin|portable monitor|tablet|soundbar|headphone|projector|keyboard|mouse/i;
const RISKY_CONDITION = /open[\s-]?box|refurb|renewed|repackag|pre[\s-]?owned|\bused\b|b[\s-]?grade|display unit|demo/i;
const SKIP_LINE = /emi|\/mo|per month|month|cashback|sav(e|ing)|\boff\b|coupon|exchange|discount|delivery|shipping|instant|bonus|joining/i;
const OUT_OF_STOCK = /out of stock|sold out|currently unavailable|no longer available|temporarily unavailable|notify me when available/i;

const CUR = R.currency;                                        // '₹' or '$'
const CUR_RE = CUR === '₹' ? /(?:₹|Rs\.?)\s?([\d,]{4,10}(?:\.\d+)?)/g : /\$\s?([\d,]{3,7}(?:\.\d{2})?)/g;
const CUR_IN_LINE = CUR === '₹' ? /₹|Rs\./ : /\$/;
const money = (s) => { const m = String(s).replace(/,/g, '').match(/\d+(?:\.\d+)?/); return m ? Math.round(parseFloat(m[0])) : 0; };
const amountsIn = (line) => [...line.matchAll(CUR_RE)].map((m) => Math.round(parseFloat(m[1].replace(/,/g, '')))).filter((n) => n >= R.minAmount);
const fmt = (n) => CUR + Math.round(n).toLocaleString(R.numberLocale);
const median = (a) => { const s = [...a].sort((x, y) => x - y); const m = s.length >> 1; return s.length % 2 ? s[m] : (s[m - 1] + s[m]) / 2; };
// "Amazon.com", "DealSea · Amazon" and "amazon" are the same retailer
const retailerOf = (name) => String(name).toLowerCase().replace(/^dealsea · /, '').replace(/\.(com|in)$/, '').replace(/[^a-z0-9&]/g, '');
const esc = (s) => String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');

function modelKey(title) {
  const t = title.toUpperCase().replace(/[™®‎‏]/g, '');
  // Samsung: the same panel is sold as "LS27FG500SN" (retailers) and "Odyssey OLED G5 G50SF" (Samsung's own pages);
  // fold both into size + Odyssey code (27G50SF) so they get compared with each other.
  const ls = t.match(/\bLS(\d{2})([A-Z])G(\d)(\d)\d[A-Z]{2}/);
  if (ls) return `${ls[1]}G${ls[3]}${ls[4]}S${ls[2]}`;
  const ody = t.match(/\bG([3-9])(\d)S([A-Z])\b/);
  if (ody) { const size = t.match(/\b(\d{2})(?:\.\d)?\s?(?:"|”|″|''|-?\s?INCH|IN\b)/); return `${size ? size[1] : ''}G${ody[1]}${ody[2]}S${ody[3]}`; }
  // Acer: family+size code (VG277U, X27U, XV275K); the trailing "Xbiip"/"W1bmiipprx" is just a bundle variant
  const acer = /ACER|NITRO|PREDATOR/.test(t) && t.match(/\b((?:VG|XV|XB|XZ|KG|CB|X)\d{2,3}[A-Z]{0,2})\b/);
  if (acer) return acer[1];
  const pats = [
    [/\bAW\d{4}[A-Z]{1,3}\b/, (m) => m[0]],                                 // Alienware
    [/\bAG\d{3}[A-Z0-9]{3,5}\b/, (m) => m[0]],                              // AOC Agon
    [/\bQ\d{2}G[A-Z0-9]{2,4}\b/, (m) => m[0]],                              // AOC Q27G..
    [/\b\d{2}G[A-Z]\d{2,3}[A-Z]{0,2}(?:-[A-Z])?\b/, (m) => m[0].replace(/-[A-Z]$/, '')], // LG 27GX790A
    [/\b(MAG|MPG|MEG)\s?(\d{3}[A-Z]{2,5})\b/, (m) => m[1] + m[2]],          // MSI
    [/\bX?G\d{2}[A-Z]{3,}[A-Z0-9]*\b/, (m) => m[0]],                        // ASUS XG27AQDMG
    [/\bPG\d{2}[A-Z]{3,}[A-Z0-9]*\b/, (m) => m[0]],
    [/\bXG\d{4}\b/, (m) => m[0]],                                           // ViewSonic
    [/\bF[OC]\d{2}[A-Z]\d[A-Z]?\b/, (m) => m[0]],                           // Gigabyte
    [/\bCO\d{2}DQ\b/, (m) => m[0]],
    [/\bEX\d{3}UZ\b/, (m) => m[0]],                                         // BenQ
    [/27Q-10/, () => 'LEGION27Q-10'],
  ];
  for (const [re, f] of pats) { const m = t.match(re); if (m) return f(m); }
  return null;
}
// No model code in the title (e.g. Best Buy's "Acer - Predator 27" QD-OLED QHD 240Hz"): group by brand + size +
// resolution + refresh so the listing still shows up in the cheapest-prices table. Never used for alerts,
// because different models share the same specs.
const BRANDS = /\b(ACER|ALIENWARE|DELL|ASUS|SAMSUNG|LG|MSI|GIGABYTE|AORUS|AOC|PHILIPS|HP|OMEN|LENOVO|CORSAIR|SONY|BENQ|VIEWSONIC|KTC|INNOCN|SCEPTRE|XIAOMI|ZOWIE)\b/;
function specKey(title) {
  const t = title.toUpperCase();
  const brand = (t.match(BRANDS) || [])[1]; const size = (t.match(/\b(\d{2})(?:\.\d)?\s?(?:"|”|″|''|-?\s?INCH|IN\b)/) || [])[1];
  if (!brand || !size) return null;
  const res = /4K|UHD|3840/.test(t) ? '4K' : /5K|5120/.test(t) ? '5K' : /QHD|1440|2560/.test(t) ? 'QHD' : /FHD|1080/.test(t) ? 'FHD' : '';
  const hz = Math.max(0, ...[...t.matchAll(/(\d{3})\s?HZ/g)].map((m) => +m[1]));
  return `~${brand} ${size}" ${res}${hz ? ' ' + hz + 'Hz' : ''}`.replace(/\s+/g, ' ');
}
const seeds = Object.fromEntries(Object.entries(cfg.streetPriceSeeds || {}).map(([k, v]) => [modelKey(k) || k, v]));

// ---------- page extractors (run inside the browser) ----------
const amazonExtract = () => [...document.querySelectorAll('[data-component-type="s-search-result"]')].map((e) => ({
  title: (e.querySelector('h2') || {}).innerText || '',
  price: (e.querySelector('.a-price .a-offscreen') || {}).textContent || '',
  mrp: (e.querySelector('.a-price.a-text-price .a-offscreen') || {}).textContent || '',
  url: e.dataset.asin ? location.origin + '/dp/' + e.dataset.asin : '',
}));

const flipkartExtract = () => [...document.querySelectorAll('a[href*="/p/itm"]')].map((a) => {
  const c = a.closest('[data-id]') || a.parentElement.parentElement;
  const text = c.innerText.replace(/\n+/g, ' | ');
  const title = a.getAttribute('title') || (c.innerText.split('\n').find((l) => l.length > 25) || '');
  return { title, text, url: a.href.split('?')[0] };
});

const bestbuyExtract = () => [...document.querySelectorAll('a.product-list-item-link')].map((a) => {
  const c = a.closest('li') || a.parentElement.parentElement;
  const text = c.innerText.split('\n').join(' | ');
  const title = (c.querySelector('h2, h3, .product-title') || {}).innerText || a.innerText;
  return { title, text, url: a.href.split('?')[0] };
});

// generic product-card extractor: title = longest OLED line without a price, url = the card's product link
const cardsExtract = (sel) => [...document.querySelectorAll(sel)].map((e) => {
  const lines = e.innerText.split('\n').map((l) => l.trim()).filter(Boolean);
  const title = lines.filter((l) => /oled/i.test(l) && l.length >= 20 && l.length <= 250 && !l.includes('$')).sort((a, b) => b.length - a.length)[0] || '';
  const links = [...e.querySelectorAll('a[href]')].filter((x) => !/signin|account\.|javascript:|#/.test(x.href) && x.href.length > 30);
  const a = links.find((x) => /\/p\/N|\/ip\/|\.product\.|\/c\/product\/|\/product\//.test(x.href)) || links[0];
  return { title, text: lines.join(' | '), url: a ? a.href.split('?')[0] : '' };
});

// DealSea: community-posted deals; each box = title, price, "Retailer $price". Expired boxes are skipped.
const dealseaExtract = () => [...document.querySelectorAll('.dealbox')].map((e) => {
  const lines = e.innerText.split('\n').map((l) => l.trim()).filter(Boolean);
  const a = e.querySelector('a[href^="/view-deal/"]');
  const sm = lines.map((l) => l.match(/^(.+?)\s+\$[\d,.]+$/)).find(Boolean);
  return { title: lines[0] || '', price: lines.find((l) => /^\$[\d,.]+$/.test(l)) || '', store: sm ? sm[1] : '',
    expired: /expired/i.test(e.className + ' ' + e.innerText.slice(0, 200)), url: a ? 'https://dealsea.com' + a.getAttribute('href') : '' };
});

const anchorsExtract = () => [...document.querySelectorAll('a[href]')].map((a) => [(a.innerText || a.title || '').trim().slice(0, 120), a.href]).filter(([t]) => t.length > 15);

// Free-text listing pages: find OLED monitor title lines, then read the prices under each one.
//  'labeled' (US): the first "$x" / "From $x" line is the price; was/MSRP/estimated-value lines are the reference.
//  'minmax' (India): lowest amount under the title is the price, highest the MRP, skipping EMI/cashback lines.
function parseTextBlocks(text, anchors, fallbackUrl) {
  const lines = text.split('\n').map((l) => l.trim()).filter(Boolean);
  const isTitle = (l) => /oled/i.test(l) && l.length >= 20 && l.length <= 220 && !CUR_IN_LINE.test(l) && MONITOR_OK.test(l) && !NOT_MONITOR.test(l);
  const out = [];
  for (let i = 0; i < lines.length; i++) {
    if (!isTitle(lines[i])) continue;
    let price = 0; let mrp = 0;
    if (R.textParser === 'minmax') {
      const nums = [];
      for (let j = i + 1; j < Math.min(lines.length, i + 10); j++) {
        if (isTitle(lines[j])) break;
        if (SKIP_LINE.test(lines[j]) && !/mrp|total price|original price/i.test(lines[j])) continue;
        nums.push(...amountsIn(lines[j]));
      }
      if (!nums.length) continue;
      price = Math.min(...nums); mrp = Math.max(...nums);
    } else {
      const prices = []; const refs = [];
      for (let j = i + 1; j < Math.min(lines.length, i + 14); j++) {
        const l = lines[j];
        if (isTitle(l) || /^(save|compare|view product page|quick view|add to cart|buy)$/i.test(l)) break;
        if (/\/mo\b|per month|financ|\bapr\b|earn|back in|rewards/i.test(l)) continue;
        const am = amountsIn(l); if (!am.length) continue;
        if (/estimated value|\bwas\b|msrp|list price|original price|reg(ular)?\.? price/i.test(l)) refs.push(...am);
        else if (/^(from |now )?\$/i.test(l)) prices.push(am[0]);
      }
      if (!prices.length) continue;
      price = prices[0]; mrp = Math.max(0, ...refs);
    }
    const key = lines[i].slice(0, 22).toLowerCase();
    const code = (lines[i].match(/\b[A-Z]{1,3}\d{2,4}[A-Z0-9]{0,6}\b/g) || []).pop();
    const hit = anchors.find(([, h]) => code && h.toLowerCase().includes(code.toLowerCase())) ||
      anchors.find(([t]) => t.toLowerCase().startsWith(key) || lines[i].toLowerCase().startsWith(t.toLowerCase().slice(0, 22)));
    out.push({ title: lines[i], price, mrp: mrp > price ? mrp : 0, url: hit ? hit[1] : fallbackUrl });
  }
  return out;
}

// ---------- scrape ----------
const BLOCKED = /captcha|robot check|access denied|unusual traffic|enter the characters|security verification|verify you are (a )?human|are you a human|just a moment|robot or human|503 - service unavailable|rush hour and traffic/i;

async function scrapeSource(ctx, src) {
  const items = []; const errors = [];
  const page = await ctx.newPage();
  for (const url of src.urls) {
    try {
      // some sites (Amazon from datacenter IPs) block at random: retry with fresh cookies and a growing pause
      let body = '', blocked = true, tries = 0;
      while (blocked && tries < (src.retries || 1)) {
        if (tries) { await ctx.clearCookies(); await page.waitForTimeout(4000 + tries * 3000); }
        tries++;
        await page.goto(url, { waitUntil: 'domcontentloaded', timeout: 45000 });
        await page.waitForTimeout(4000);
        for (let i = 0; i < 5; i++) { await page.mouse.wheel(0, 1600); await page.waitForTimeout(400); }
        body = await page.evaluate(() => document.body.innerText);
        blocked = BLOCKED.test(body.slice(0, 1500)) || BLOCKED.test(await page.title());
      }
      if (src.retries) console.log('TRIES', src.name, url, tries, blocked ? 'still blocked' : 'ok');
      if (blocked) { errors.push('blocked/captcha'); continue; }
      const before = items.length;
      if (src.kind === 'amazon') {
        for (const r of (await page.evaluate(amazonExtract)).filter((x) => x.price.includes(CUR))) items.push({ title: r.title, price: money(r.price), mrp: money(r.mrp), url: r.url });
      } else if (src.kind === 'flipkart' || src.kind === 'bestbuy') {
        for (const r of await page.evaluate(src.kind === 'bestbuy' ? bestbuyExtract : flipkartExtract)) {
          const a = amountsIn(r.text); if (!a.length) continue;
          items.push({ title: r.title, price: a[0], mrp: a[1] > a[0] ? a[1] : 0, url: r.url });
        }
      } else if (src.kind === 'dealsea') {
        for (const r of await page.evaluate(dealseaExtract)) if (!r.expired && r.price) items.push({ title: r.title, price: money(r.price), mrp: 0, url: r.url, store: r.store });
      } else if (src.kind === 'cards') {
        const mk = (v) => [].concat(v || []).map((x) => new RegExp(x, 'i'));
        const priceRes = mk(src.priceRe); const refRes = mk(src.refRe);
        const firstMatch = (res, t) => { for (const re of res) { const m = t.match(re); if (m) return m; } return null; };
        await page.waitForTimeout(src.wait || 0);
        for (const r of await page.evaluate(cardsExtract, src.sel)) {
          const pm = firstMatch(priceRes, r.text); if (!pm) continue;
          const rm = firstMatch(refRes, r.text);
          items.push({ title: r.title, price: money(pm[1]), mrp: rm ? money(rm[1]) : 0, url: r.url || url });
        }
      } else {
        items.push(...parseTextBlocks(body, await page.evaluate(anchorsExtract), url));
      }
      if (items.length === before) {
        // zero rows from a search page: record what the page really was (title, text, screenshot) so a silent bot wall shows up
        const tag = `${src.name.replace(/\W+/g, '')}-${src.urls.indexOf(url)}`;
        console.log('EMPTY', src.name, url, '| title:', await page.title(), '| text:', body.slice(0, 200).replace(/\s+/g, ' '));
        try { fs.mkdirSync('debug', { recursive: true }); await page.screenshot({ path: `debug/${tag}.png` }); } catch {}
        if (src.kind !== 'text') errors.push('0 results');
      }
    } catch (e) { errors.push(String(e.message).slice(0, 60)); }
  }
  await page.close();
  return { items, errors };
}

// Re-open a deal's product page: is the price really there, and is it in stock?
// A misread price (B&H once parsed as $60 for a $699 monitor) or a sold-out listing must not become an alert.
async function verifyDeal(ctx, it) {
  const page = await ctx.newPage();
  try {
    await page.goto(it.url, { waitUntil: 'domcontentloaded', timeout: 40000 });
    await page.waitForTimeout(5000);
    const text = await page.evaluate(() => document.body.innerText);
    if (BLOCKED.test(text.slice(0, 1500))) return 'unverified (page blocked)';
    const top = text.slice(0, 6000);
    const seen = amountsIn(text).some((n) => Math.abs(n - it.price) <= Math.max(1, it.price * 0.005));
    if (OUT_OF_STOCK.test(top) && !/add to (cart|bag)|buy now/i.test(top)) return 'out of stock';
    return seen ? 'verified' : 'unverified (price not on page)';
  } catch (e) {
    return 'unverified (page failed to load)';
  } finally { await page.close().catch(() => {}); }
}

async function main() {
  const CDP = process.env.CDP_URL;
  const ua = { locale: R.browserLocale, timezoneId: R.timeZone };
  const browser = CDP ? await chromium.connectOverCDP(CDP)
    : await chromium.launch({ headless: true, channel: process.env.BROWSER_CHANNEL || undefined, executablePath: process.env.BROWSER_PATH || undefined });
  const ctx = CDP ? browser.contexts()[0] : await browser.newContext({ ...ua, viewport: { width: 1440, height: 900 },
    userAgent: 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36' });
  // Amazon.in answers desktop browsers from GitHub's datacenter IPs with a 503 "rush hour" page; a phone-shaped browser gets real results.
  const mobileCtx = CDP ? ctx : await browser.newContext({ ...ua, isMobile: true, hasTouch: true, viewport: { width: 390, height: 844 },
    userAgent: 'Mozilla/5.0 (iPhone; CPU iPhone OS 17_5 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.5 Mobile/15E148 Safari/604.1' });

  const health = []; const all = [];
  for (const src of cfg.sources) {
    const { items, errors } = await scrapeSource(src.mobile ? mobileCtx : ctx, src);
    if (process.env.DEBUG_ITEMS) console.log(src.name, JSON.stringify(items.slice(0, 6)).slice(0, 1800));
    const good = items.filter((i) => i.title && MONITOR_OK.test(i.title) && !NOT_MONITOR.test(i.title) && /oled/i.test(i.title) &&
      i.price >= cfg.minPrice && i.price <= cfg.maxPrice);
    for (const g of good) {
      const source = g.store ? `${src.name} · ${g.store}` : src.name;
      const key = modelKey(g.title); const spec = key ? null : specKey(g.title);
      all.push({ ...g, source, retailer: retailerOf(source), feed: !!src.feed, key: key || spec, generic: !key, risky: RISKY_CONDITION.test(g.title) });
    }
    health.push({ name: src.name, found: good.length, errors: [...new Set(errors)] });
    console.log(src.name, 'raw', items.length, 'kept', good.length, errors.length ? 'ERR ' + [...new Set(errors)].join(',') : '');
  }

  // cheapest listing per (model, source, condition)
  const best = new Map();
  for (const it of all) {
    if (!it.key) continue;
    const k = it.key + '|' + it.source + '|' + (it.risky ? 'r' : 'n');
    if (!best.has(k) || best.get(k).price > it.price) best.set(k, it);
  }
  const mine = [...best.values()];

  // the other scanner's latest listings (laptop <-> GitHub) widen the comparison; they are never alerted from here
  const peer = cfg.peerSnapshot ? readJsonAt(cfg.peerSnapshot, null) : null;
  const peerAgeH = peer ? (Date.now() - Date.parse(peer.t)) / HOUR : Infinity;
  const myRetailers = new Set(mine.map((x) => x.retailer));
  const peerItems = peer && peerAgeH < 8 ? peer.items.filter((x) => !myRetailers.has(x.retailer)) : [];

  const byModel = {};
  for (const it of [...mine, ...peerItems.map((x) => ({ ...x, peer: true }))]) (byModel[it.key] ||= []).push(it);

  const history = readJson('history.json', {});
  for (const k of Object.keys(history)) {   // fold histories saved under older model keys (e.g. LS27FG502SW -> 27G50SF)
    const nk = modelKey(k);
    if (nk && nk !== k) { history[nk] = [...(history[nk] || []), ...history[k]].sort((a, b) => (a.t < b.t ? -1 : 1)).slice(-120); delete history[k]; }
  }
  const alerted = readJson('alerted.json', {});
  const peerAlerted = cfg.peerSnapshot ? readJsonAt(path.join(path.dirname(cfg.peerSnapshot), 'alerted.json'), {}) : {};
  const now = new Date().toISOString();
  const crazy = []; const near = [];
  for (const [key, list] of Object.entries(byModel)) {
    const hist = (history[key] || []).map((h) => h.price);
    const histRef = hist.length >= 6 ? median(hist) : 0;
    const lowestSeen = hist.length ? Math.min(...hist) : 0;
    for (const it of list) {
      if (it.peer || it.generic) continue;
      // "normal" = what OTHER retailers charge (never the listing itself, never deal-feed or open-box prices),
      // plus the seeded street price and this model's own price history
      const others = list.filter((x) => x.retailer !== it.retailer && !x.risky && !x.feed).map((x) => x.price);
      const signals = [...others, ...(seeds[key] ? [seeds[key]] : []), ...(histRef ? [histRef] : [])];
      if (!signals.length) continue;
      const ref = median(signals);
      const vsRef = it.price / ref; const vsHist = histRef ? it.price / histRef : 1;
      const rec = { ...it, ref, basis: signals.length, lowestSeen, pct: Math.round((1 - vsRef) * 100), suspect: vsRef < 0.25 };
      // an alert needs 2+ independent prices: a single comparison is often a brand store's list price
      // (Samsung.com "From $499" vs a normal $329 street price) and would cry wolf
      const isCrazy = vsRef <= cfg.crazyThreshold || (vsHist <= cfg.historyThreshold && vsRef < 0.9);
      if (isCrazy && signals.length >= 2) crazy.push(rec);
      else if (isCrazy || vsRef <= cfg.nearMissThreshold) near.push(rec);
    }
    // history tracks the best NORMAL price (no open-box, no deal-feed) from this scanner's own sources
    const normal = list.filter((x) => !x.peer && !x.risky && !x.feed).map((x) => x.price);
    if (normal.length) { (history[key] ||= []).push({ t: now, price: Math.min(...normal) }); history[key] = history[key].slice(-120); }
  }

  // alert only on new or ≥5% lower prices, or the same deal again after a week; skip what the other scanner already sent
  const aKey = (c) => c.key + '|' + c.retailer;
  const prevOf = (store, c) => { const v = store[aKey(c)]; return typeof v === 'number' ? { price: v, t: now } : v; };
  const isFresh = (c) => [prevOf(alerted, c), prevOf(peerAlerted, c)].every((p) => !p || c.price < p.price * 0.95 || Date.now() - Date.parse(p.t) > 7 * DAY);
  const candidates = crazy.filter(isFresh).sort((a, b) => b.pct - a.pct);

  // verify on the product page before alerting
  const fresh = []; const dropped = [];
  for (const c of candidates.slice(0, 8)) {
    const srcCfg = cfg.sources.find((s) => c.source.startsWith(s.name));
    c.check = await verifyDeal(srcCfg?.mobile ? mobileCtx : ctx, c);
    console.log('VERIFY', c.key, c.source, fmt(c.price), '->', c.check);
    if (c.check === 'out of stock' || (c.suspect && c.check !== 'verified')) dropped.push(c); else fresh.push(c);
  }
  if (VERIFY_SAMPLE) {
    for (const c of mine.filter((x) => !x.feed).sort((a, b) => a.price - b.price).slice(0, 3)) console.log('SAMPLE-VERIFY', c.key, c.source, fmt(c.price), '->', await verifyDeal(ctx, c), c.url);
  }
  if (CDP) { /* leave the user's browser running */ } else await browser.close();

  for (const c of fresh) alerted[aKey(c)] = { price: c.price, t: now };
  writeJson('history.json', history); writeJson('alerted.json', alerted);
  writeJson('snapshot.json', { t: now, items: mine.filter((x) => !x.feed).map(({ key, generic, source, retailer, price, risky, title, url }) => ({ key, generic, source, retailer, price, risky, title, url })) });

  // ---------- email ----------
  const stamp = new Date().toLocaleString(R.numberLocale, { timeZone: R.timeZone, dateStyle: 'medium', timeStyle: 'short' });
  const th = 'style="text-align:left;padding:6px 8px;background:#f3f4f6;border-bottom:1px solid #e5e7eb"';
  const td = 'style="padding:6px 8px;border-bottom:1px solid #f0f0f0;vertical-align:top"';
  const badge = (c) => !c.check ? '' : c.check === 'verified' ? '<span style="color:#15803d">✓ price + stock checked</span>' : `<span style="color:#b45309">⚠ ${esc(c.check)}</span>`;
  const row = (c) => `<tr><td ${td}><b>${esc(c.title.slice(0, 90))}</b>${c.risky ? ' <span style="color:#b45309">⚠ open-box/refurb/used?</span>' : ''}<br>${badge(c)}</td>` +
    `<td ${td}><b>${fmt(c.price)}</b></td><td ${td}>${fmt(c.ref)}<br><small style="color:#6b7280">from ${c.basis} price${c.basis > 1 ? 's' : ''}</small></td>` +
    `<td ${td}>${c.pct}% below${c.lowestSeen ? `<br><small style="color:#6b7280">lowest seen ${fmt(c.lowestSeen)}</small>` : ''}</td><td ${td}><a href="${esc(c.url)}">${esc(c.source)}</a></td></tr>`;
  const tbl = (rows) => `<table style="border-collapse:collapse;font:14px Arial;width:100%"><tr><th ${th}>Item</th><th ${th}>Price</th><th ${th}>Normal</th><th ${th}></th><th ${th}>Where</th></tr>${rows.map(row).join('')}</table>`;
  const cheapest = Object.entries(byModel).map(([key, list]) => ({ key, ...list.filter((x) => !x.peer && !x.risky).sort((a, b) => a.price - b.price)[0] }))
    .filter((x) => x.price).sort((a, b) => a.price - b.price).slice(0, 8);
  const bad = health.filter((h) => !h.found);
  let html = `<div style="font:14px Arial;max-width:820px;color:#111"><h2 style="margin:0 0 4px">${esc(R.title)}</h2><div style="color:#6b7280">${stamp} ${R.tzLabel}</div>`;
  html += fresh.length ? `<h3 style="color:#b91c1c">🚨 Crazy deals (≥${Math.round((1 - cfg.crazyThreshold) * 100)}% below what other sellers charge)</h3>${tbl(fresh)}<p>${esc(R.buyNote)}</p>`
    : `<h3>No new crazy deal this run.</h3>`;
  if (dropped.length) html += `<p style="color:#6b7280">Skipped ${dropped.length} deal${dropped.length > 1 ? 's' : ''} that failed the page check: ${dropped.map((c) => `${esc(c.key)} ${fmt(c.price)} at ${esc(c.source)} (${esc(c.check)})`).join('; ')}.</p>`;
  if (near.length) html += `<h3>Near-misses (${Math.round((1 - cfg.nearMissThreshold) * 100)}%+ below, or a bigger drop with only one price to compare)</h3>${tbl(near.sort((a, b) => b.pct - a.pct).slice(0, 8))}`;
  html += `<h3>Cheapest prices right now</h3><table style="border-collapse:collapse;font:14px Arial;width:100%"><tr><th ${th}>Model</th><th ${th}>Price</th><th ${th}>Where</th></tr>${cheapest.map((c) => `<tr><td ${td}>${esc(c.title.slice(0, 80))}</td><td ${td}><b>${fmt(c.price)}</b>${c.mrp > c.price ? ` <s style="color:#6b7280">${fmt(c.mrp)}</s>` : ''}</td><td ${td}><a href="${esc(c.url)}">${esc(c.source)}</a></td></tr>`).join('')}</table>`;
  html += `<h3>Source health</h3><ul>${health.map((h) => `<li>${h.found ? '✅' : '❌'} ${esc(h.name)}: ${h.found} items${h.errors.length ? ' (' + esc(h.errors.join(', ')) + ')' : ''}</li>`).join('')}`;
  if (cfg.peerSnapshot) html += `<li>${peerAgeH < 26 ? '✅' : '⚠️'} ${esc(cfg.peerLabel)}: ${peer ? `last ran ${peerAgeH < 1 ? 'under an hour' : Math.round(peerAgeH) + 'h'} ago, ${peer.items.length} listings` : 'no run recorded yet'}${peerAgeH >= 26 ? ' (not running: is the laptop on?)' : ''}</li>`;
  html += `</ul><p style="color:#6b7280">${esc(R.footer)}</p></div>`;
  const subject = fresh.length ? `🚨 ${R.subjectTag} crazy deal: ${fresh[0].title.slice(0, 40)} ${fmt(fresh[0].price)} (${fresh[0].pct}% below)`
    : `${R.subjectTag} digest ${stamp}: no crazy deal (${cheapest[0] ? 'low ' + fmt(cheapest[0].price) : 'no data'})${bad.length > 3 ? ' ⚠ many sources failed' : ''}`;

  if (DRY) {
    console.log('\nSUBJECT:', subject, '\nCRAZY', fresh.length, 'DROPPED', dropped.length, 'NEAR', near.length, 'PEER', peerItems.length,
      '\nCHEAPEST', cheapest.map((c) => `${c.key} ${c.price} ${c.source}`), '\nNEAR', near.map((c) => `${c.key} ${c.price} ${c.source} ref ${c.ref} (${c.basis})`));
    fs.writeFileSync('last-email.html', html); return;
  }
  const hourNow = Number(new Date().toLocaleString('en-US', { timeZone: R.timeZone, hour: 'numeric', hour12: false }));
  const dailyDigest = (R.dailyDigestHours || []).includes(hourNow);
  if (cfg.emailMode === 'alerts-only' && !fresh.length && !dailyDigest && !process.env.FORCE_EMAIL) { console.log('no alert; skipping email'); return; }
  if (process.env.MAIL_VIA_GH) {
    const { execFileSync } = await import('node:child_process');
    execFileSync('gh', ['workflow', 'run', 'mail.yml', '-R', process.env.MAIL_VIA_GH, '--json'], { input: JSON.stringify({ subject, html }) });
    console.log('email relayed via GitHub:', subject);
    return;
  }
  const { GMAIL_USER, GMAIL_APP_PASSWORD, MAIL_TO } = process.env;
  if (!GMAIL_USER || !GMAIL_APP_PASSWORD || !MAIL_TO) throw new Error('Missing GMAIL_USER / GMAIL_APP_PASSWORD / MAIL_TO');
  const tx = nodemailer.createTransport({ host: 'smtp.gmail.com', port: 465, secure: true, auth: { user: GMAIL_USER, pass: GMAIL_APP_PASSWORD } });
  await tx.sendMail({ from: `${R.title} <${GMAIL_USER}>`, to: MAIL_TO, subject, html });
  console.log('email sent:', subject);
}
main().then(() => process.exit(0)).catch((e) => { console.error(e); process.exit(1); });
