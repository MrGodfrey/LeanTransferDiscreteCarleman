(function (root) {
  'use strict';
  const proofLabel = { PLANNED: '计划中', SPECIFIED: '陈述完成', BUILT: '构建通过 · 待核对', REVIEWED: '语义核对完成' };
  const scopeLabel = { PAPER: '原文命题', CONDITIONAL: '条件性命题', AUXILIARY: '辅助引理' };
  const buildLabel = { NOT_RUN: '未执行', PASS: '通过', FAIL: '失败', RUNNING: '执行中', CANCELLED: '已取消' };
  const stateLabel = { IDLE: '当前无在途任务', RUNNING: '云端任务正在执行', REVIEW: '成果待审', BLOCKED: '当前目标有阻塞', PAUSED: '已暂停' };
  const phaseLabel = { TODO: '待开始', IN_PROGRESS: '进行中', VERIFIED: '已验收', BLOCKED: '有阻塞' };
  const stale = (s, hours, now) => !s || !Number.isFinite(Date.parse(s)) || Date.parse(s) > now + 60000 || now - Date.parse(s) > hours * 3600000;
  function model(d, now = Date.now()) {
    const snapshotStale = stale(d.snapshot.synced_at, 24, now);
    const executionStale = stale(d.execution.supervisor_checked_at, 12, now) || snapshotStale;
    const running = d.execution.state === 'RUNNING';
    return {
      snapshotStale, executionStale,
      live: running && !executionStale,
      executionText: running && executionStale ? '最近记录为运行中，当前状态待更新' : (stateLabel[d.execution.state] || '状态待核实'),
      paperDone: d.coverage.filter(c => c.scope === 'PAPER' && c.verification_status === 'REVIEWED' && c.extra_hypotheses.length === 0 && c.paper_complete).length,
      conditional: d.claims.filter(c => c.scope === 'CONDITIONAL' && ['BUILT', 'REVIEWED'].includes(c.verification_status)).length
    };
  }
  if (typeof module !== 'undefined' && module.exports) module.exports = { model };
  if (typeof document === 'undefined') return;
  const d = root.LEAN_TRANSFER_STATUS;
  if (!d) { document.body.textContent = '缺少快照，请运行 python3 tools/update_dashboard.py'; return; }
  const $ = id => document.getElementById(id);
  const set = (id, value) => { $(id).textContent = value ?? '—'; };
  const node = (tag, value, className) => { const e = document.createElement(tag); e.textContent = value ?? ''; if (className) e.className = className; return e; };
  const date = s => s ? new Date(s).toLocaleString('zh-CN', { timeZone: 'Asia/Shanghai', hour12: false }) : '尚未记录';
  const short = s => s ? s.slice(0, 12) : '尚无记录';
  function addLink(parent, url, title) {
    if (!url) return;
    try { if (new URL(url).protocol !== 'https:') return; } catch { return; }
    const a = node('a', title, 'evidence-link'); a.href = url; a.target = '_blank'; a.rel = 'noopener noreferrer'; parent.appendChild(a);
  }
  function renderBuild(parent, b, title) {
    parent.appendChild(node('h3', title, 'miniheading'));
    if (!b) { parent.appendChild(node('p', '尚无成功构建记录', 'section-note')); return; }
    parent.appendChild(node('p', `${buildLabel[b.status]} · ${short(b.checked_sha)} · ${date(b.finished_at)}`, 'evidence-text'));
    parent.appendChild(node('p', `Lean：${b.lean_version || '尚未配置'}；mathlib：${short(b.mathlib_commit)}；目标：${b.targets.join(', ') || '尚未配置'}`, 'evidence-text'));
    addLink(parent, b.ci_url, '打开 CI 证据 ↗');
  }
  function renderProof(parent, c, title, ref) {
    const row = node('article', '', 'proof-row');
    const head = node('div', '', 'proof-head');
    head.append(node('h3', title), node('span', `${scopeLabel[c.scope]} · ${proofLabel[c.verification_status]}`, c.scope === 'CONDITIONAL' ? 'conditional-text' : ''));
    row.append(head, node('p', `${c.id} · ${c.milestone} · ${ref}`, 'claim-ref'));
    if (c.lean_declarations.length) row.append(node('p', c.lean_declarations.join(' · '), 'declarations'));
    if (c.extra_hypotheses.length) row.append(node('p', '额外前提：' + c.extra_hypotheses.join('；'), 'conditional-text'));
    if (c.blocker) row.append(node('p', '阻塞：' + c.blocker, 'blocker-text'));
    if (c.dependencies?.length) row.append(node('p', '依赖目标：' + c.dependencies.join('、'), 'claim-ref'));
    if (c.declaration_version) row.append(node('p', '声明版本：' + short(c.declaration_version), 'claim-ref'));
    if (c.build_evidence) {
      row.append(node('p', `构建：${buildLabel[c.build_evidence.status]} · ${short(c.build_evidence.checked_sha)} · ${c.build_evidence.targets.join(', ')}`, 'claim-ref'));
      addLink(row, c.build_evidence.ci_url, '构建证据 ↗');
    }
    if (c.review_recorded) row.append(node('p', '语义/依赖核对已记录：' + date(c.reviewed_at), 'claim-ref'));
    addLink(row, c.review_url, '核对记录 ↗'); addLink(row, c.pr_url, 'PR ↗');
    parent.appendChild(row);
  }
  function refreshClocks() {
    const v = model(d);
    set('syncBadge', !d.snapshot.synced_at ? '尚未同步' : v.snapshotStale ? '快照待更新' : '已记录快照');
    $('syncBadge').className = 'badge ' + (!d.snapshot.synced_at ? 'gray' : v.snapshotStale ? 'yellow' : 'green');
    set('executionState', v.executionText);
    set('executionNote', v.executionStale ? '执行状态未获近期核实；此页面展示最近保存的记录。' : '依据最近监督核实；不是实时连接。');
    document.querySelector('.live-dot').classList.toggle('running', v.live);
  }
  const v = model(d);
  set('lastUpdate', '快照：' + date(d.snapshot.synced_at));
  set('footerTimestamp', `${d.snapshot.mode} · ${short(d.snapshot.source_commit)} · Asia/Shanghai`);
  set('auditedCount', v.paperDone); set('auditedSub', '/ ' + d.coverage.length + ' 个原文具名结果');
  set('conditionalCount', v.conditional);
  set('milestoneCount', d.milestones.filter(m => m.status === 'VERIFIED').length + ' / ' + d.milestones.length);
  set('buildStatus', buildLabel[d.verification.latest_build.status]);
  set('buildCommit', '本次检查：' + short(d.verification.latest_build.checked_sha));
  set('taskName', d.execution.task_title || '未启动');
  set('lastCommit', short(d.verification.last_successful_build?.checked_sha));
  set('supervisorChecked', date(d.execution.supervisor_checked_at));
  set('nextAction', d.execution.next_action);
  set('currentBlocker', d.execution.blocker || '尚无已登记阻塞');
  addLink($('taskLinks'), d.execution.pr_url, '当前 PR ↗');
  const phase = d.milestones.find(m => m.status === 'IN_PROGRESS');
  set('activePhase', phase ? phase.id : '尚无进行中阶段');
  d.milestones.forEach(m => {
    const row = node('div', '', 'milestone-row'); const info = node('div', '', 'phase-info');
    info.append(node('b', m.title), node('small', m.description));
    if (m.blocker) info.append(node('p', '阻塞：' + m.blocker, 'blocker-text'));
    row.append(node('div', m.id, 'phase-num'), info, node('span', phaseLabel[m.status], 'phase-status'));
    $('milestoneRows').append(row);
  });
  set('claimSummary', d.claims.length + ' 个初始工作目标 · 不作为全文完成率');
  d.claims.forEach(c => renderProof($('claimsRows'), c, c.title, c.paper_ref + (c.paper_labels.length ? ' · ' + c.paper_labels.join(', ') : '')));
  d.coverage.forEach(c => renderProof($('coverageRows'), c, c.paper_result, `${c.paper_label} · PDF p.${c.pdf_page}`));
  renderBuild($('buildEvidence'), d.verification.latest_build, '最近一次构建');
  renderBuild($('buildEvidence'), d.verification.last_successful_build, '最近一次成功构建');
  if (!d.events.length) $('activityList').appendChild(node('p', '暂无正式运行记录，等待 M0a 启动。', 'empty'));
  d.events.slice(0, 7).forEach(e => { const row = node('div', '', 'event'); row.append(node('b', e.summary), node('small', date(e.at))); addLink(row, e.url, '证据 ↗'); $('activityList').append(row); });
  refreshClocks(); setInterval(refreshClocks, 60000);
})(typeof window === 'undefined' ? globalThis : window);
