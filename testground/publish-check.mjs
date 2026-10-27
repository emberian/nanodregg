// publish-check.mjs URL SHOT [--live] — the published page in Chromium (Playwright from ~/tools/playwright;
// testground/PUBLISH.md §3 and §5). The desktop renders, "Start here" step 1 (`alice$ nd create`) ends
// `exit ok`, the Writer menu exists, and the World window's kernel sha256 is the tab's own hash of the
// bytes it runs and kernel.json's. With --live, the door: the desktop's "Join the live World" joins the
// deployment's live World (enrolled, first sync ok, the roster read off the tab's own fold holds the
// visitor and the guest-book, the Frames window shows the visitor's frames); a reload returns the SAME member
// from the browser's storage, re-derived; "Forget me" leaves nothing kept. SHOT is a path prefix for
// the screenshots. Exit 0 only if every check holds; the JSON on stdout says which did not.
const { chromium } = await import(process.env.PLAYWRIGHT_PATH ?? '/Users/ember/tools/playwright/node_modules/playwright/index.mjs');
const [url, shot] = process.argv.slice(2).filter((a) => !a.startsWith('--'));
const live = process.argv.includes('--live');
const browser = await chromium.launch({ executablePath: process.env.CHROMIUM_PATH });
const ctx = await browser.newContext({ viewport: { width: 1280, height: 900 } });
const page = await ctx.newPage();
const logs = [];
page.on('console', (m) => logs.push(`${m.type()}: ${m.text()}`));
page.on('pageerror', (e) => logs.push(`pageerror: ${e.message}`));
page.on('dialog', (d) => d.accept());
const res = { url, checks: {} };
const check = (k, v, detail) => { res.checks[k] = v ? 'ok' : `FAILED${detail === undefined ? '' : `: ${detail}`}`; return v; };
const exits = () => page.evaluate(() => [...document.querySelectorAll('div.dim')].map((d) => d.innerText).filter((t) => /^exit \w+ ·/.test(t)));
const dbl = (label) => page.evaluate((l) => [...document.querySelectorAll('#icons .icon')].find((b) => b.innerText.includes(l)).click(), label);
const termText = () => page.evaluate(() => document.querySelector('.term .out')?.innerText ?? '');
try {
  const t0 = Date.now();
  await page.goto(url, { waitUntil: 'load' });
  await page.waitForSelector('#tasks button', { timeout: 30000 });
  res.desktopMs = Date.now() - t0;
  res.icons = await page.locator('#icons .icon .label').allInnerTexts();
  const k = await page.evaluate(() => window.testground.kernel);
  res.kernel = { sha256: k.sha256, commit: k.built?.commit, stamped: k.built?.sha256, tree: k.built?.tree };
  check('kernel sha256 is the tab\'s and kernel.json\'s', k.sha256 && k.sha256 === k.built?.sha256, JSON.stringify(res.kernel));
  check('the World window shows the kernel sha256', (await page.locator('#desktop').innerText()).includes(k.sha256));
  check('Writer menu', (await page.locator('fieldset.writer select#writer-lie option').count()) > 1);
  await dbl('Start here');
  await page.waitForSelector('.tour li button.btn', { timeout: 10000 });
  const before = (await exits()).length;
  await page.locator('.tour li button.btn').first().click();
  await page.waitForFunction((n) => [...document.querySelectorAll('div.dim')].filter((d) => /^exit \w+ ·/.test(d.innerText)).length > n, before, { timeout: 20000 });
  check('tour step 1 exit ok', (await exits()).some((e) => e.startsWith('exit ok')), (await exits()).join(' | '));
  await page.waitForTimeout(300);
  await page.screenshot({ path: `${shot}-desktop.png` });
  if (live) {
    check('the door icon', res.icons.includes('Join the live World'), res.icons.join(', '));
    const tj = Date.now();
    await dbl('live World');
    await page.waitForFunction(() => /^exit \w+ ·/m.test(document.querySelector('.term .out')?.innerText ?? '') && /Enrolled\. member/.test(document.querySelector('.term .out')?.innerText ?? '') && document.querySelectorAll('.term .out div.dim').length >= 2, null, { timeout: 60000 });
    await page.waitForFunction(() => [...document.querySelectorAll('.term .out div.dim')].filter((d) => /^exit \w+ ·/.test(d.innerText)).length >= 2, null, { timeout: 60000 });
    res.joinMs = Date.now() - tj;
    const ex = await exits();
    check('joined: init and first sync ok', ex.length >= 2 && ex.every((e) => e.startsWith('exit ok')), ex.join(' | '));
    const st = await page.evaluate(() => { const w = window.testground.world(); return { me: w.members[0]?.id, sponsor: w.wj?.sponsor, origin: w.origin, roster: window.testground.roster(), frames: window.testground.frames().length, address: location.search }; });
    res.member = st.me; res.origin = st.origin; res.roster = { count: st.roster?.members.length, height: st.roster?.height };
    check('roster holds you and the guest-book', st.roster?.members.includes(st.me) && st.roster?.members.includes(st.sponsor), JSON.stringify(res.roster));
    check('the Frames window shows your frames', st.frames > 0 && (await page.locator('.log .row').count()) > 0, st.frames);
    check('the address is the door (?live)', st.address === '?live', st.address);
    const keptRec = await page.evaluate(() => Object.keys(localStorage).filter((x) => x.startsWith('nd-testground/member ')));
    check('membership kept in storage', keptRec.length === 1, keptRec.join(', '));
    await page.screenshot({ path: `${shot}-live.png` });
    // come back: a reload of the door is the same member, re-derived from the invitation
    const tr = Date.now();
    await page.reload({ waitUntil: 'load' });
    await page.waitForFunction(() => /Welcome back/.test(document.querySelector('.term .out')?.innerText ?? '') && [...document.querySelectorAll('.term .out div.dim')].some((d) => /^exit \w+ ·/.test(d.innerText)), null, { timeout: 60000 });
    res.returnMs = Date.now() - tr;
    const back = await page.evaluate(() => ({ me: window.testground.world().members[0]?.id, roster: window.testground.roster() }));
    const ex2 = await exits();
    check('returned as the same member, sync ok', back.me === st.me && ex2.at(-1)?.startsWith('exit ok'), `${back.me} vs ${st.me}; ${ex2.join(' | ')}`);
    check('the returned member is in its own fold', back.roster?.members.includes(st.me));
    await page.waitForTimeout(300);
    await page.screenshot({ path: `${shot}-return.png` });
    await page.getByRole('button', { name: 'Forget me', exact: true }).click();
    await page.getByRole('button', { name: 'Confirm Forget me', exact: true }).click();
    await page.waitForSelector('.tour li button.btn', { timeout: 10000 });
    const after = await page.evaluate(() => Object.keys(localStorage).filter((x) => x.startsWith('nd-testground/member ')).length);
    check('Forget me leaves nothing kept', after === 0, after);
    check('the door says Join again', (await page.locator('#door-label').innerText()) === 'Join the live World');
  }
} catch (e) {
  check('ran to the end', false, e.message.split('\n')[0]);
  await page.screenshot({ path: `${shot}-error.png` }).catch(() => {});
}
res.errors = logs.filter((l) => /error/i.test(l));
res.ok = Object.values(res.checks).every((v) => v === 'ok');
console.log(JSON.stringify(res, null, 1));
await browser.close();
process.exit(res.ok ? 0 : 1);
