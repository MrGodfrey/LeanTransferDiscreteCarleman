const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const vm = require('node:vm');
const { model } = require('../docs/app.js');
const now = Date.parse('2026-10-17T10:00:00Z');
function data() {
  return {snapshot: {synced_at:'2026-10-17T09:00:00Z'}, execution:{state:'RUNNING',supervisor_checked_at:'2026-10-17T09:00:00Z'}, coverage:[], claims:[]};
}
test('reviewed conditional remains conditional, never counted as paper', () => {
  const d = data(); d.claims = [{scope:'CONDITIONAL',verification_status:'REVIEWED',extra_hypotheses:['bridge'],paper_complete:false}];
  assert.equal(model(d, now).conditional, 1); assert.equal(model(d, now).paperDone, 0);
});
test('extra hypothesis disqualifies paper even if a bad completion flag is supplied', () => {
  const d = data(); d.coverage = [{scope:'PAPER',verification_status:'REVIEWED',extra_hypotheses:['bridge'],paper_complete:true}];
  assert.equal(model(d, now).paperDone, 0);
});
test('stale supervisor check removes running light even with a fresh snapshot', () => {
  const d = data(); d.execution.supervisor_checked_at = '2026-10-16T09:00:00Z';
  assert.equal(model(d, now).live, false); assert.match(model(d, now).executionText, /当前状态待更新/);
});
test('missing or invalid check timestamp is stale', () => {
  for (const value of [null, 'invalid', '2027-01-01T00:00:00Z']) {
    const d = data(); d.execution.supervisor_checked_at = value; assert.equal(model(d, now).live, false);
  }
});
test('an old snapshot never represents live execution', () => {
  const d = data(); d.snapshot.synced_at = '2026-10-15T00:00:00Z'; assert.equal(model(d, now).live, false);
});
test('fresh verified running state and explicit pause are distinct', () => {
  const d = data(); assert.equal(model(d, now).live, true);
  d.execution.state = 'PAUSED'; assert.equal(model(d, now).executionText, '已暂停'); assert.equal(model(d, now).live, false);
});
test('generated JavaScript is executable and excludes account data', () => {
  const context = {window:{}}; vm.runInNewContext(fs.readFileSync(require.resolve('../docs/data.js'),'utf8'),context);
  const d = context.window.LEAN_TRANSFER_STATUS;
  assert.equal(d.schema_version, 2); assert.equal(d.coverage.length, 26); assert.equal('usage' in d, false);
});
test('the renderer binds every referenced element and builds both registries', () => {
  // Offline DOM contract check; not a browser or a visual layout test.
  class Element {
    constructor() { this.children = []; this.textContent = ''; this.className = ''; this.classes = new Set(); this.classList = {toggle:(key,on)=>on?this.classes.add(key):this.classes.delete(key)}; }
    append(...children) { this.children.push(...children); }
    appendChild(child) { this.children.push(child); return child; }
  }
  const html = fs.readFileSync(require.resolve('../docs/index.html'),'utf8');
  const ids = [...html.matchAll(/\bid="([^"]+)"/g)].map(m=>m[1]);
  assert.equal(ids.length,new Set(ids).size);
  const elements = Object.fromEntries(ids.map(id=>[id,new Element()]));
  const light = new Element();
  const context = {window:{}, document:{getElementById:id=>elements[id] || null,createElement:()=>new Element(),querySelector:selector=>selector==='.live-dot'?light:null},setInterval:()=>0};
  vm.runInNewContext(fs.readFileSync(require.resolve('../docs/data.js'),'utf8'),context);
  vm.runInNewContext(fs.readFileSync(require.resolve('../docs/app.js'),'utf8'),context);
  assert.equal(elements.claimsRows.children.length,19);
  assert.equal(elements.coverageRows.children.length,26);
  assert.equal(elements.auditedCount.textContent,0);
  assert.equal(light.classes.has('running'),false);
  assert.match(elements.executionState.textContent,/当前无在途任务/);
});
