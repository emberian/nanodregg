// Chromium checks for the compositor. No server or kernel needed.
import { readFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import assert from 'node:assert/strict';
const { chromium } = await import(process.env.PLAYWRIGHT_PATH ?? '/Users/ember/tools/playwright/node_modules/playwright/index.mjs');
const root = fileURLToPath(new URL('.', import.meta.url));
const browser = await chromium.launch({headless:true, executablePath:process.env.CHROMIUM_PATH});
const page = await browser.newPage({viewport:{width:1280,height:900}});
await page.route('http://127.0.0.1/**', async route=>{
  const path=new URL(route.request().url()).pathname.slice(1);
  if(path==='fixture') return route.fulfill({contentType:'text/html',body:`<link rel="stylesheet" href="testground.css"><div id="desktop" tabindex="0"></div><div id="taskbar"><div id="tasks"></div></div><script type="module">
    import {compositor} from './compositor.js';
    const $=(tag,a={},...kids)=>{const e=document.createElement(tag);for(const[k,v]of Object.entries(a))e.setAttribute(k,v);for(const k of kids.flat(Infinity))e.append(k instanceof Node?k:String(k));return e;};
    window.wm=compositor({desk:document.querySelector('#desktop'),tasks:document.querySelector('#tasks'),$});
    window.openTest=(id='test-a',extra={})=>wm.openWindow({id,title:id,x:100,y:100,w:420,h:300,body:$('div',{},$('input',{'aria-label':'input'}),$('p',{},'Selectable content')), ...extra});
  </script>`});
  try { await route.fulfill({body:await readFile(root+path),contentType:path.endsWith('.js')?'text/javascript':'text/css'}); }
  catch { await route.fulfill({status:404,body:'missing'}); }
});
const errors=[];page.on('pageerror',e=>errors.push(e.message));
const report={};
try {
  await page.goto('http://127.0.0.1/fixture'); await page.waitForFunction(()=>window.wm);
  await page.evaluate(()=>openTest());
  const state=()=>page.evaluate(()=>{const o=wm.wins.get('test-a');return {x:o.x,y:o.y,w:o.w,h:o.h};});
  const drag=async(selector,dx,dy)=>{
    const r=await page.locator(selector).boundingBox(),x=r.x+r.width/2,y=r.y+r.height/2;
    await page.mouse.move(x,y);await page.mouse.down();await page.mouse.move(x+dx,y+dy,{steps:8});await page.mouse.up();
  };
  for(const edge of ['n','ne','e','se','s','sw','w','nw']){
    const before=await state();
    await drag('.resize-handle.'+edge,edge.includes('w')?-17:edge.includes('e')?17:0,edge.includes('n')?-17:edge.includes('s')?17:0);
    const after=await state();assert.notDeepEqual(after,before,'resize '+edge);
  }
  report.edges=8;
  await drag('.titlebar .title',-2000,-2000);let r=await state();assert.equal(r.x,0);assert.equal(r.y,0);
  await drag('.titlebar .title',2000,2000);r=await state();assert.equal(r.x+r.w,1280);assert.equal(r.y+r.h,await page.evaluate(()=>document.querySelector('#desktop').clientHeight));
  report.clamped=true;
  await page.locator('[data-action="minimize"]').click();assert.equal(await page.locator('.window:visible').count(),0);
  await page.locator('#tasks button').click();assert.equal(await page.locator('.window:visible').count(),1);
  await page.evaluate(()=>openTest('test-b',{x:80,y:80}));
  await page.locator('[data-window="test-b"] .titlebar').focus();
  await page.keyboard.press('Tab');assert.equal(await page.evaluate(()=>document.activeElement.closest('[data-window]').dataset.window),'test-a');
  const before=await state();await page.keyboard.press('ArrowLeft');assert.equal((await state()).x,before.x-1);
  await page.keyboard.press('Enter');
  assert.equal(await page.evaluate(()=>document.activeElement.tagName),'INPUT','title enters content without a Tab trap');
  await page.locator('[data-window="test-a"] input').focus();await page.keyboard.press('ArrowLeft');assert.equal((await state()).x,before.x-1);
  await page.evaluate(()=>openTest('transient',{dialog:true}));await page.keyboard.press('Escape');assert.equal(await page.locator('[data-window="transient"]').count(),0);
  report.keyboard=true;
  await page.evaluate(()=>{const a=wm.wins.get('test-a');wm.focus(a);openTest('background',{activate:false});});
  assert(await page.evaluate(()=>+wm.wins.get('test-a').el.style.zIndex > +wm.wins.get('background').el.style.zIndex),'background content stays below active window');
  await page.evaluate(()=>wm.clear());await page.evaluate(()=>openTest());
  assert.deepEqual(await state(),await page.evaluate(()=>JSON.parse(localStorage.getItem('nd-testground/layout/1/test'))));
  await page.setViewportSize({width:360,height:480});await page.waitForTimeout(50);
  r=await state();assert(r.x>=0&&r.x+r.w<=360&&r.y>=0&&r.y+r.h<=440);
  await page.setViewportSize({width:1280,height:900});
  await page.evaluate(()=>{wm.clear();localStorage.clear();openTest();});
  await page.locator('.titlebar .title').dblclick();assert(await page.evaluate(()=>!!wm.wins.get('test-a').restore));
  await page.locator('.titlebar .title').dblclick();assert.equal((await state()).h,300);
  // Simulate pointer movement at display cadence. Measure actual rendered frames, not event count.
  await page.evaluate(()=>{window.samples=[];window.sampling=true;const f=t=>{samples.push(t);if(sampling)requestAnimationFrame(f);};requestAnimationFrame(f);});
  for(let i=0;i<2;i++)await drag('.titlebar .title',i?-200:200,0);
  const times=await page.evaluate(()=>{sampling=false;return samples;});
  report.dragFps=times.length>1?1000*(times.length-1)/(times.at(-1)-times[0]):0;
  // Closing during a drag must release global listeners too.
  await page.evaluate(()=>wm.clear());
  const cdp=await page.context().newCDPSession(page);
  await cdp.send('HeapProfiler.collectGarbage');await cdp.send('Performance.enable');
  const metrics=async()=>({...(await cdp.send('Memory.getDOMCounters')),heap:(await cdp.send('Performance.getMetrics')).metrics.find(x=>x.name==='JSHeapUsedSize').value});
  report.before=await metrics();
  await page.evaluate(()=>{for(let i=0;i<50;i++){const o=openTest('cycle-'+i);o.bar.dispatchEvent(new PointerEvent('pointerdown',{bubbles:true,button:0,pointerId:1,clientX:110,clientY:110}));o.close();}});
  await page.waitForTimeout(50);await cdp.send('HeapProfiler.collectGarbage');report.after=await metrics();
  assert.equal(report.after.jsEventListeners,report.before.jsEventListeners,'listeners released after 50 closes');
  assert.equal(await page.locator('.window').count(),0);
  // Storage denied: the desktop remains usable.
  await page.evaluate(()=>{Storage.prototype.getItem=()=>{throw Error('denied');};Storage.prototype.setItem=()=>{throw Error('denied');};openTest().close();});
  assert.deepEqual(errors,[]);
  report.ok=true;
} finally { console.log(JSON.stringify(report,null,2));await browser.close(); }
