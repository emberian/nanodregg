// UI journeys and measurements against the built page, served by Playwright routing.
import { readFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import assert from 'node:assert/strict';
const { chromium }=await import(process.env.PLAYWRIGHT_PATH??'/Users/ember/tools/playwright/node_modules/playwright/index.mjs');
const root=fileURLToPath(new URL('.',import.meta.url));
const browser=await chromium.launch({executablePath:process.env.CHROMIUM_PATH});
const page=await browser.newPage({viewport:{width:1280,height:900}});
await page.route('http://127.0.0.1/**',async route=>{
  const name=new URL(route.request().url()).pathname.slice(1)||'index.html';
  try{await route.fulfill({body:await readFile(root+name),contentType:name.endsWith('.wasm')?'application/wasm':/\.m?js$/.test(name)?'text/javascript':name.endsWith('.css')?'text/css':name.endsWith('.json')?'application/json':'text/html'});}
  catch{await route.fulfill({status:404,body:'not found'});}
});
const errors=[];page.on('pageerror',e=>errors.push(e.message));
const report={};
const focus=async id=>page.locator('#tasks [data-window="'+id+'"]').click();
try{
  const t=Date.now();await page.goto('http://127.0.0.1/');await page.waitForFunction(()=>window.testground);
  report.interactiveMs=Date.now()-t;
  await focus('term-alice');
  const input=page.getByRole('textbox',{name:"alice's nd command"});
  await input.fill('create');await input.press('Enter');
  await page.waitForFunction(()=>document.querySelector('[data-window="term-alice"] .out').textContent.includes('exit ok'));
  assert.equal(await page.evaluate(()=>document.activeElement.getAttribute('aria-label')),"alice's nd command",'tour update keeps terminal focus');
  await page.getByRole('button',{name:'Editor',exact:true}).click();
  const editor=page.locator('[data-window="editor-main"]');
  await editor.getByRole('textbox',{name:'package source'}).fill('a draft');
  await page.getByRole('button',{name:'Editor',exact:true}).click();
  assert.equal(await editor.getByRole('textbox',{name:'package source'}).inputValue(),'a draft','reopen keeps source');
  await editor.locator('[data-action="close"]').click();
  await focus('world');
  const world=page.locator('[data-window="world"]'),origin=await page.evaluate(()=>testground.world().origin??testground.world().text);
  await world.getByRole('button',{name:'New World (genesis)',exact:true}).click();
  assert.equal(await page.evaluate(()=>testground.world().origin??testground.world().text),origin,'confirmation does not reset');
  await world.getByRole('button',{name:'Cancel',exact:true}).click();
  await world.getByRole('button',{name:'New World (genesis)',exact:true}).click();
  await world.getByRole('button',{name:'Confirm New World (genesis)',exact:true}).click();
  assert.notEqual(await page.evaluate(()=>testground.world().origin??testground.world().text),origin);
  await focus('world');await world.getByRole('button',{name:'Join a hosted World…'}).click();
  const join=page.locator('[data-window="join"]');
  await join.getByRole('textbox',{name:'Relay address'}).fill('https://wrong.test/');
  await join.getByRole('textbox',{name:'Relay address'}).press('Enter');
  assert.match(await join.innerText(),/Enter ws/);
  await page.keyboard.press('Escape');assert.equal(await join.count(),0);
  await page.evaluate(()=>testground.T.openGrammar());
  const grammar=page.locator('[data-window="grammar"]');
  await grammar.getByRole('tab').first().focus();await page.keyboard.press('ArrowRight');
  assert.equal(await grammar.getByRole('tab').nth(1).getAttribute('aria-selected'),'true');
  await grammar.locator('[data-action="close"]').click();
  // Retained application listeners and DOM after opening/closing fifty terminals/editors.
  const cdp=await page.context().newCDPSession(page);await cdp.send('Performance.enable');
  await page.evaluate(()=>{for(const o of [...testground.desktop.wins.values()])o.close();});
  const metrics=async()=>{await cdp.send('HeapProfiler.collectGarbage');return {...await cdp.send('Memory.getDOMCounters'),heap:(await cdp.send('Performance.getMetrics')).metrics.find(x=>x.name==='JSHeapUsedSize').value};};
  report.before=await metrics();
  for(let i=0;i<50;i++){
    await page.evaluate(()=>document.querySelector('#icon-m0').click());
    await page.locator('[data-window="term-alice"] [data-action="close"]').click();
  }
  report.after=await metrics();assert.equal(report.after.jsEventListeners,report.before.jsEventListeners,'closed terminals release listeners');
  // Text at 125%: browser zoom changes the CSS viewport and scales the type/hit geometry.
  for(const theme of ['light','dark']){
    await page.emulateMedia({colorScheme:theme});await page.setViewportSize({width:1024,height:720});
    await page.evaluate(()=>{document.body.style.zoom='1.25';document.querySelector('#icon-m0').click();});
    await page.waitForTimeout(60);
    const sizes=await page.locator('[data-window="term-alice"] button').evaluateAll(bs=>bs.map(b=>({w:b.getBoundingClientRect().width,h:b.getBoundingClientRect().height})));
    assert(sizes.every(x=>x.w>=24&&x.h>=24));
    await page.screenshot({path:(process.env.UI_SHOT??'.ui-check/ui')+'-'+theme+'-125.png'});
    await page.locator('[data-window="term-alice"] [data-action="close"]').click();
  }
  assert.deepEqual(errors,[]);report.ok=true;
}finally{console.log(JSON.stringify(report,null,2));await browser.close();}
