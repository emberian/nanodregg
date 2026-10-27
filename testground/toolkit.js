// Shared native controls. Application state belongs to their callers.
export function element(tag, attrs = {}, ...kids) {
  const e = document.createElement(tag);
  if (tag === 'button') e.type = 'button';
  for (const [k,v] of Object.entries(attrs)) {
    if (k === 'class') e.className = v;
    else if (k.startsWith('on')) e.addEventListener(k.slice(2), v);
    else if (v !== false && v != null) e.setAttribute(k, v === true ? '' : v);
  }
  for (const k of kids.flat(Infinity)) if (k != null) e.append(k instanceof Node ? k : String(k));
  if (tag === 'a' && !attrs.href && attrs.onclick) {
    e.setAttribute('role','button'); e.tabIndex=0;
    e.addEventListener('keydown', ev => { if (ev.key === 'Enter' || ev.key === ' ') { ev.preventDefault(); e.click(); } });
  }
  return e;
}
export function confirmAction(label, message, act) {
  const $=element, status=$('span', {class:'confirmation',hidden:true}), trigger=$('button',{class:'btn'},label);
  const cancel=()=>{status.hidden=true;trigger.hidden=false;trigger.focus();};
  const yes=$('button',{class:'btn'},'Confirm '+label);
  yes.addEventListener('click',async()=>{
    if(yes.disabled)return;
    yes.disabled=true;
    try { await act(); status.hidden=true;trigger.hidden=false; }
    finally {yes.disabled=false;}
  });
  status.append($('span',{},message),yes,$('button',{class:'btn',onclick:cancel},'Cancel'));
  status.addEventListener('keydown',e=>{if(e.key==='Escape'){e.stopPropagation();e.preventDefault();cancel();}});
  trigger.addEventListener('click',()=>{trigger.hidden=true;status.hidden=false;yes.focus();});
  return $('span',{class:'confirm-action'},trigger,status);
}
let tabNo=0;
export function tabs(items, selected=0) {
  const $=element, id='tabs-'+(++tabNo), panel=$('div',{role:'tabpanel',id:id+'-panel',tabindex:'0'});
  const list=$('div',{class:'tabs',role:'tablist'}), controls=[];
  function select(i,focus=false){
    selected=i;
    controls.forEach((b,j)=>{b.setAttribute('aria-selected',String(i===j));b.tabIndex=i===j?0:-1;b.classList.toggle('on',i===j);});
    panel.setAttribute('aria-labelledby',id+'-'+i);panel.replaceChildren(items[i].body());
    if(focus)controls[i].focus();
  }
  items.forEach((item,i)=>{
    const b=$('button',{role:'tab',id:id+'-'+i,'aria-controls':id+'-panel',onclick:()=>select(i)},item.label);
    b.addEventListener('keydown',e=>{
      const j=e.key==='ArrowRight'?(i+1)%items.length:e.key==='ArrowLeft'?(i+items.length-1)%items.length:e.key==='Home'?0:e.key==='End'?items.length-1:null;
      if(j!=null){e.preventDefault();select(j,true);}
    });controls.push(b);list.append(b);
  });
  select(selected);return $('div',{},list,panel);
}
export function submitForm(action, ...kids) {
  return element('form',{onsubmit:e=>{e.preventDefault();action();}},...kids);
}

// Preserve the user's draft and reading position across a data refresh.
// A field's aria-label is its stable identity within this content view.
export function refreshContent(box, content, state) {
  const fields = root => [...root.querySelectorAll('input:not([type="range"]), textarea, select')];
  const fieldKey = (e, i) => e.tagName + ':' + (e.getAttribute('aria-label') ?? e.name ?? i) + ':' + i;
  const current = document.activeElement;
  let focus = null;
  fields(box).forEach((e, i) => {
    const k = fieldKey(e, i);
    state.fields ??= new Map();
    state.fields.set(k, { value: e.value, checked: e.checked });
    if (e === current) focus = { k, start: e.selectionStart, end: e.selectionEnd };
  });
  const expanded = [...box.querySelectorAll('details')].map(e => e.open);
  const top = box.scrollTop, left = box.scrollLeft;
  box.replaceChildren(content);
  fields(box).forEach((e, i) => {
    const k = fieldKey(e, i), old = state.fields?.get(k);
    if (old) { e.value = old.value; if ('checked' in e) e.checked = old.checked; }
    if (focus?.k === k) {
      e.focus({ preventScroll: true });
      if (focus.start != null && e.setSelectionRange) e.setSelectionRange(focus.start, focus.end);
    }
  });
  [...box.querySelectorAll('details')].forEach((e, i) => { if (expanded[i] != null) e.open = expanded[i]; });
  box.scrollTop = top; box.scrollLeft = left;
}
