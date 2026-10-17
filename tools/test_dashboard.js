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
function currentDisplay() {
  const context = {window:{}}; vm.runInNewContext(fs.readFileSync(require.resolve('../docs/data.js'),'utf8'),context);
  return context.window.LEAN_TRANSFER_STATUS;
}
test('generated JavaScript is executable and represents the current registries', () => {
  const d = currentDisplay();
  const coverage = JSON.parse(fs.readFileSync(require.resolve('../state/paper_coverage.json'),'utf8'));
  const progress = JSON.parse(fs.readFileSync(require.resolve('../state/progress.json'),'utf8'));
  assert.equal(d.schema_version, 2);
  assert.equal(d.coverage.length, coverage.results.length);
  assert.equal(d.claims.length, progress.claims.length);
  assert.equal('usage' in d, false);
});
function render(d) {
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
  const context = {window:{LEAN_TRANSFER_STATUS:d}, Date:class extends Date { static now() { return now; } }, URL,
    document:{getElementById:id=>elements[id] || null,createElement:()=>new Element(),querySelector:selector=>selector==='.live-dot'?light:null},setInterval:()=>0};
  vm.runInNewContext(fs.readFileSync(require.resolve('../docs/app.js'),'utf8'),context);
  return {elements,light};
}
function initialDisplay() {
  // Explicit test-only state, independent of the runtime ledger and generated data.
  const proof = {id:'fixture',milestone:'M1',title:'Fixture',paper_ref:'Fixture',paper_labels:[],
    paper_result:'Fixture',paper_label:'fixture',pdf_page:1,scope:'PAPER',verification_status:'PLANNED',
    extra_hypotheses:[],paper_complete:false,lean_declarations:[],declaration_version:null,
    build_evidence:null,review_recorded:false,dependencies:[],blocker:null};
  return {snapshot:{synced_at:null,source_commit:null,mode:'FIXTURE'},
    execution:{state:'IDLE',supervisor_checked_at:null,task_title:null,pr_url:null,next_action:'Start',blocker:null},
    verification:{latest_build:{status:'NOT_RUN',checked_sha:null,finished_at:null,lean_version:null,mathlib_commit:null,targets:[]},last_successful_build:null},
    milestones:[],claims:[{...proof,scope:'AUXILIARY'}],coverage:[proof],events:[]};
}
test('the current renderer follows actual data without fixing progress or task state', () => {
  const d = currentDisplay();
  const {elements,light} = render(d);
  const expected = model(d,now);
  assert.equal(elements.claimsRows.children.length,d.claims.length);
  assert.equal(elements.coverageRows.children.length,d.coverage.length);
  assert.equal(elements.auditedCount.textContent,expected.paperDone);
  assert.equal(light.classes.has('running'),expected.live);
  assert.equal(elements.executionState.textContent,expected.executionText);
});
test('an independent initial-state fixture is idle with zero completed results', () => {
  const {elements,light} = render(initialDisplay());
  assert.equal(elements.auditedCount.textContent,0);
  assert.equal(light.classes.has('running'),false);
  assert.match(elements.executionState.textContent,/当前无在途任务/);
});
test('the renderer accepts added claims, completed paper results and a running task', () => {
  const d = initialDisplay();
  d.snapshot.synced_at = '2026-10-17T09:00:00Z';
  Object.assign(d.execution,{state:'RUNNING',supervisor_checked_at:'2026-10-17T09:00:00Z',task_title:'Next proof'});
  Object.assign(d.coverage[0],{verification_status:'REVIEWED',paper_complete:true});
  d.claims.push({...d.claims[0],id:'conditional',scope:'CONDITIONAL',verification_status:'REVIEWED',extra_hypotheses:['bridge']});
  const {elements,light} = render(d);
  assert.equal(elements.claimsRows.children.length,2);
  assert.equal(elements.coverageRows.children.length,1);
  assert.equal(elements.auditedCount.textContent,1);
  assert.equal(elements.conditionalCount.textContent,1);
  assert.equal(light.classes.has('running'),true);
  assert.equal(elements.executionState.textContent,'云端任务正在执行');
});
