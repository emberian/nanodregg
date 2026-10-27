// One owner for window geometry, focus order and lifetime.
const limits = {term:[320,180,360], world:[320,220,480], log:[320,200,320], editor:[360,260,580], lesson:[360,260,660], tutorial:[340,240,600], obj:[340,240,540], pkg:[340,220,480], turn:[340,220,520]};
const clamp = (n,a,b) => Math.max(a,Math.min(n,b));
const rect = o => ({x:o.x,y:o.y,w:o.w,h:o.h});
const key = k => 'nd-testground/layout/1/'+k;
const saved = k => { try { const r=JSON.parse(localStorage.getItem(key(k))); return r && ['x','y','w','h'].every(k=>Number.isFinite(r[k])) ? r:null; } catch { return null; } };
export function compositor({desk,tasks,$,dispose=()=>{}}) {
  const wins=new Map();
  let active=null, cascade=0, gesture=null;
  const bounds=()=>({w:desk.clientWidth,h:desk.clientHeight});
  const constrain=(o,r,b=bounds())=>{
    r.w=clamp(r.w,Math.min(o.minW,b.w),b.w); r.h=clamp(r.h,Math.min(o.minH,b.h),b.h);
    r.x=clamp(r.x,0,b.w-r.w); r.y=clamp(r.y,0,b.h-r.h); return r;
  };
  const paint=o=>{
    Object.assign(o.el.style,{left:o.x+'px',top:o.y+'px',width:o.w+'px',height:o.h+'px',transform:''});
    o.el.hidden=o.minimized;
  };
  const remember=o=>{try{localStorage.setItem(key(o.kind),JSON.stringify(o.restore??rect(o)));}catch{/* optional storage */}};
  const stack=()=>{
    let z=1;
    for(const o of wins.values()){
      o.el.style.zIndex=z++;
      o.el.classList.toggle('focused',o===active&&!o.minimized);
      o.task.classList.toggle('on',o===active&&!o.minimized);
      o.task.setAttribute('aria-pressed',String(o===active&&!o.minimized));
      o.task.title=o.title+(o.minimized?' (minimized)':'');
    }
  };
  function focus(o,keyboard=false){
    if(!wins.has(o.id))return;
    o.minimized=false; o.el.hidden=false;
    if(active!==o){wins.delete(o.id);wins.set(o.id,o);active=o;}
    stack(); if(keyboard)o.bar.focus({preventScroll:true});
  }
  const successor=()=>{
    active=[...wins.values()].reverse().find(o=>!o.minimized)??null;
    stack(); active?.bar.focus({preventScroll:true});
  };
  function endGesture(commit=true){
    if(!gesture)return;
    const g=gesture;gesture=null;g.abort.abort();cancelAnimationFrame(g.raf);
    g.o.el.classList.remove('moving'); if(!commit)Object.assign(g.o,g.start);
    paint(g.o);if(commit)remember(g.o);
  }
  function close(o){
    if(!wins.has(o.id))return;
    const hadFocus=o.el.contains(document.activeElement)||active===o;
    if(gesture?.o===o)endGesture();
    remember(o);wins.delete(o.id);o.closed=true;o.life.abort();dispose(o.el);dispose(o.task);o.el.remove();o.task.remove();o.onClose?.();
    if(hadFocus)successor();
  }
  function minimize(o){if(gesture?.o===o)endGesture();o.minimized=true;paint(o);successor();}
  function zoom(o){
    if(o.restore){Object.assign(o,constrain(o,o.restore));o.restore=null;}
    else{
      o.restore=rect(o);
      const child=o.body.firstElementChild,b=bounds();
      Object.assign(o,constrain(o,{x:o.x,y:o.y,w:Math.max(o.w,(child?.scrollWidth??0)+24),h:Math.max(o.minH,o.body.scrollHeight+o.bar.offsetHeight+12)},b));
    }
    paint(o);remember(o);
  }
  function openWindow({id,title,kind=id.split('-')[0],x,y,w=420,h,body,onClose,dialog=false,activate=true}){
    const old=wins.get(id);
    if(old){if(onClose!==undefined)old.onClose=onClose;old.setBody(body);old.setTitle(title);if(activate)focus(old);return old;}
    const [minW,minH,defaultH]=limits[kind]??[280,160,420];
    const bodyBox=$('div',{class:'body'},body),titleEl=$('span',{class:'title'},title);
    const button=(a,t,g)=>$('button',{type:'button','data-action':a,title:t,'aria-label':t},g);
    const bar=$('div',{class:'titlebar',tabindex:'0',title:'Drag to move. Double-click to fit content. Tab changes windows. Enter enters controls. Arrows move. Ctrl+arrows resize. Shift uses 10 pixels.'},titleEl,button('minimize','Minimize','−'),button('zoom','Fit content','□'),button('close','Close','×'));
    const el=$('section',{class:'window',role:'region','aria-label':title,'data-window':id},bar,bodyBox);
    for(const edge of ['n','ne','e','se','s','sw','w','nw'])el.append($('div',{class:'resize-handle '+edge,'data-edge':edge,'aria-hidden':'true'}));
    const task=$('button',{type:'button',title,'data-window':id},title),pos=cascade++%8,life=new AbortController();
    const o={id,kind,title,el,bar,body:bodyBox,task,minW,minH,minimized:false,closed:false,life,onClose,transient:dialog,
      ...constrain({minW,minH},saved(kind)??{x:x??110+pos*26,y:y??16+pos*22,w,h:h??defaultH}),
      setBody(b){if(!o.closed&&b!=null){for(const child of bodyBox.children)dispose(child);bodyBox.replaceChildren(b);}},
      setTitle(t){o.title=t;titleEl.textContent=t;task.textContent=t;el.setAttribute('aria-label',t);task.title=t;},
      close:()=>close(o),focus:()=>focus(o,true)};
    wins.set(id,o);
    if(!activate&&active){wins.delete(active.id);wins.set(active.id,active);}
    desk.append(el);tasks.append(task);paint(o);if(activate)focus(o);else stack();return o;
  }
  function snap(o,r,edge,b,others){
    const xs=[0,b.w],ys=[0,b.h],threshold=8;
    for(const q of others){
      if(r.y<q.y+q.h+threshold&&r.y+r.h>q.y-threshold)xs.push(q.x,q.x+q.w);
      if(r.x<q.x+q.w+threshold&&r.x+r.w>q.x-threshold)ys.push(q.y,q.y+q.h);
    }
    const delta=(vs,ts)=>{let best=threshold+1,d=0;for(const v of vs)for(const t of ts)if(Math.abs(t-v)<best){best=Math.abs(t-v);d=t-v;}return best<=threshold?d:0;};
    if(!edge){r.x+=delta([r.x,r.x+r.w],xs);r.y+=delta([r.y,r.y+r.h],ys);}
    else{
      if(edge.includes('w')){const d=delta([r.x],xs);r.x+=d;r.w-=d;}
      if(edge.includes('e'))r.w+=delta([r.x+r.w],xs);
      if(edge.includes('n')){const d=delta([r.y],ys);r.y+=d;r.h-=d;}
      if(edge.includes('s'))r.h+=delta([r.y+r.h],ys);
    }
    return constrain(o,r,b);
  }
  desk.addEventListener('pointerdown',e=>{
    const o=wins.get(e.target.closest('[data-window]')?.dataset.window);if(!o)return;focus(o);
    const edge=e.target.dataset.edge;
    if(e.button!==0||(!edge&&(!e.target.closest('.titlebar')||e.target.closest('button'))))return;
    e.preventDefault();o.bar.focus({preventScroll:true});endGesture();
    const start=rect(o),b=bounds(),abort=new AbortController(),others=[...wins.values()].filter(q=>q!==o&&!q.minimized).map(rect);
    const g=gesture={o,start,abort,raf:0,px:e.clientX,py:e.clientY};o.el.classList.add('moving');
    const update=m=>{
      let r=rect(start),dx=m.clientX-g.px,dy=m.clientY-g.py;
      if(!g.moved && Math.abs(dx)+Math.abs(dy)<3)return;
      g.moved=true;o.restore=null;
      if(!edge){r.x+=dx;r.y+=dy;}
      else{
        if(edge.includes('e'))r.w=clamp(start.w+dx,Math.min(o.minW,b.w),b.w-start.x);
        if(edge.includes('s'))r.h=clamp(start.h+dy,Math.min(o.minH,b.h),b.h-start.y);
        if(edge.includes('w')){r.x=clamp(start.x+dx,0,start.x+start.w-Math.min(o.minW,b.w));r.w=start.x+start.w-r.x;}
        if(edge.includes('n')){r.y=clamp(start.y+dy,0,start.y+start.h-Math.min(o.minH,b.h));r.h=start.y+start.h-r.y;}
      }
      Object.assign(o,snap(o,r,edge,b,others));
      if(!g.raf)g.raf=requestAnimationFrame(()=>{g.raf=0;if(edge)paint(o);else o.el.style.transform='translate('+(o.x-start.x)+'px, '+(o.y-start.y)+'px)';});
    };
    const opt={signal:abort.signal};
    window.addEventListener('pointermove',m=>{if(m.pointerId===e.pointerId)update(m);},opt);
    window.addEventListener('pointerup',m=>{if(m.pointerId===e.pointerId){update(m);endGesture();}},opt);
    window.addEventListener('pointercancel',()=>endGesture(false),opt);
    window.addEventListener('blur',()=>endGesture(),opt);
  });
  desk.addEventListener('focusin',e=>{const o=wins.get(e.target.closest('[data-window]')?.dataset.window);if(o)focus(o);});
  desk.addEventListener('click',e=>{
    const b=e.target.closest('[data-action]'),o=wins.get(b?.closest('[data-window]')?.dataset.window);if(o)({close,minimize,zoom})[b.dataset.action]?.(o);
  });
  desk.addEventListener('dblclick',e=>{
    if(!e.target.closest('.titlebar')||e.target.closest('button'))return;
    const o=wins.get(e.target.closest('[data-window]')?.dataset.window);if(o)zoom(o);
  });
  tasks.addEventListener('click',e=>{const o=wins.get(e.target.closest('[data-window]')?.dataset.window);if(o)focus(o,true);});
  document.addEventListener('keydown',e=>{
    if(e.defaultPrevented)return;
    if(e.key==='Escape'){if(gesture){e.preventDefault();endGesture(false);}else if(active?.transient){e.preventDefault();close(active);}return;}
    const onTitle=e.target===active?.bar;
    if(onTitle&&e.key==='Enter'){
      e.preventDefault();
      (active.body.querySelector('input:not(:disabled),textarea:not(:disabled),select:not(:disabled),button:not(:disabled),a[href],[tabindex="0"]')??active.bar.querySelector('button')).focus();
    }
    if(e.key==='Tab'&&(onTitle||e.target===desk||e.altKey)){
      const list=[...wins.values()].filter(o=>!o.minimized).sort((a,b)=>a.id.localeCompare(b.id));if(!list.length)return;
      e.preventDefault();focus(list[(list.indexOf(active)+(e.shiftKey?list.length-1:1))%list.length],true);
    }
    if(onTitle&&['ArrowLeft','ArrowRight','ArrowUp','ArrowDown'].includes(e.key)){
      e.preventDefault();active.restore=null;const r=rect(active),n=e.shiftKey?10:1;
      const dx=e.key==='ArrowLeft'?-n:e.key==='ArrowRight'?n:0,dy=e.key==='ArrowUp'?-n:e.key==='ArrowDown'?n:0;
      if(e.ctrlKey){r.w+=dx;r.h+=dy;}else{r.x+=dx;r.y+=dy;}
      Object.assign(active,constrain(active,r));paint(active);remember(active);
    }
  });
  new ResizeObserver(()=>{endGesture();for(const o of wins.values()){Object.assign(o,constrain(o,rect(o)));paint(o);}}).observe(desk);
  return {wins,focus,openWindow,clear:()=>{for(const o of [...wins.values()])close(o);}};
}
