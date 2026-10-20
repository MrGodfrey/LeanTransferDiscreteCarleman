#!/usr/bin/env python3
"""Validate record consistency and project an explicit display schema; not a proof verifier."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import sys
from datetime import datetime, timezone
from urllib.parse import urlsplit

ROOT = Path(__file__).resolve().parents[1]
SHA = re.compile(r'[0-9a-f]{40}')
PROOF_STATES = {'PLANNED', 'SPECIFIED', 'BUILT', 'REVIEWED'}
SCOPES = {'PAPER', 'CONDITIONAL', 'AUXILIARY'}
BUILD_STATES = {'NOT_RUN', 'PASS', 'FAIL', 'RUNNING', 'CANCELLED'}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(value):
    return isinstance(value, str) and SHA.fullmatch(value) is not None


def text(value):
    require(value is None or isinstance(value, str), 'display text must be a string or null')
    return value


def timestamp(value):
    if value is None:
        return
    require(isinstance(value, str), 'timestamp must be a string')
    parsed = datetime.fromisoformat(value.replace('Z', '+00:00'))
    require(parsed.tzinfo is not None, 'timestamp must include timezone')


def https_url(value):
    if not isinstance(value, str):
        return False
    try:
        p = urlsplit(value)
        return p.scheme == 'https' and bool(p.hostname) and not p.username and not p.password
    except ValueError:
        return False


def strings(values):
    require(isinstance(values, list) and all(isinstance(v, str) and v for v in values), 'expected nonempty string elements')
    return list(values)


def validate_build(b):
    require(b['status'] in BUILD_STATES, 'invalid build status')
    source = b.get('source', 'github')
    require(source in {'local', 'github'}, 'invalid build source')
    strings(b['targets'])
    timestamp(b['finished_at'])
    if b['status'] != 'NOT_RUN':
        require(sha(b['checked_sha']), 'build needs full checked_sha')
        if source == 'local':
            require(b.get('ci_url') is None, 'local build must not claim a CI run')
        else:
            require(https_url(b['ci_url']), 'build needs actual HTTPS CI reference')
        require(bool(b['targets']), 'build needs target names')
    if b['status'] in {'PASS', 'FAIL', 'CANCELLED'}:
        require(b['finished_at'], 'completed build needs time')
    if b['status'] == 'PASS':
        require(b['lean_version'] and sha(b['mathlib_commit']), 'PASS needs toolchain evidence')
        if source == 'local':
            digest = lambda value: isinstance(value, str) and re.fullmatch(r'[0-9a-f]{64}', value)
            require(digest(b.get('source_manifest_sha256')), 'local PASS needs source manifest digest')
            commands = b.get('commands')
            require(isinstance(commands, list) and commands and all(
                isinstance(c, dict) and isinstance(c.get('command'), str) and c['command'].strip()
                and type(c.get('exit_code')) is int and c['exit_code'] == 0 for c in commands),
                'local PASS needs actual successful commands')
            audit = b.get('axiom_audit', {})
            require(isinstance(audit, dict) and audit.get('status') == 'PASS'
                    and type(audit.get('declarations')) is int and audit['declarations'] > 0
                    and digest(audit.get('sha256')), 'local PASS needs axiom audit evidence')


def validate_proof(c):
    require(c['verification_status'] in PROOF_STATES and c['scope'] in SCOPES, 'invalid proof axes')
    names = strings(c['lean_declarations'])
    strings(c['extra_hypotheses'])
    if c['verification_status'] in {'BUILT', 'REVIEWED'}:
        require(names and sha(c['declaration_version']), f"{c['id']}: missing declaration version")
        b = c['build_evidence']
        require(isinstance(b, dict), f"{c['id']}: missing build evidence")
        validate_build(b)
        require(b['status'] == 'PASS' and b['checked_sha'] == c['declaration_version'], 'build does not match declaration version')
    if c['verification_status'] == 'REVIEWED':
        review = c['semantic_review']
        require(isinstance(review, dict), f"{c['id']}: missing semantic review")
        require(review.get('result') == 'PASS' and review.get('axiom_check') == 'PASS', 'review/axiom check required')
        require(review.get('checked_sha') == c['declaration_version'], 'stale semantic review')
        require(set(strings(review['declarations'])) == set(names), 'review declarations mismatch')
        require(isinstance(review.get('review_ref'), str) and review['review_ref'].strip(), 'review reference required')
        require(review.get('reviewed_at'), 'review time required')
        timestamp(review['reviewed_at'])


def complete(c):
    # Called only after validate; all evidence is bound to the declared version.
    return c['scope'] == 'PAPER' and c['verification_status'] == 'REVIEWED' and not c['extra_hypotheses']


def unique(rows, name):
    ids = [row['id'] for row in rows]
    require(len(ids) == len(set(ids)), f'duplicate {name}')
    return set(ids)


def validate(x, coverage):
    require(x['schema_version'] == 2 and coverage['schema_version'] == 1, 'unsupported schema')
    require('usage' not in x, 'retired account data must not be stored')
    require(x['execution']['state'] in {'IDLE', 'RUNNING', 'REVIEW', 'BLOCKED', 'PAUSED'}, 'invalid execution state')
    timestamp(x['execution']['supervisor_checked_at'])
    timestamp(x['snapshot']['synced_at'])
    if x['snapshot']['source_commit'] is not None:
        require(sha(x['snapshot']['source_commit']), 'invalid snapshot SHA')
    require(coverage['source_tex_sha256'] == x['project']['source_tex_sha256'], 'paper source mismatch')
    for u in x['dashboard']['approved_urls']:
        require(https_url(u), 'display URL must be HTTPS without credentials')
    mids = unique(x['milestones'], 'milestone')
    cids = unique(x['claims'], 'claim')
    tids = unique(x['tasks'], 'task')
    unique(coverage['results'], 'paper result')
    goal_ids = cids | {c['id'] for c in coverage['results']}
    require(len({c['paper_label'] for c in coverage['results']}) == len(coverage['results']), 'duplicate paper label')
    current = x['execution']['current_task_id']
    require(current is None or current in tids, 'unknown current task')
    if x['execution']['state'] in {'RUNNING', 'REVIEW'}:
        require(current is not None, 'active state needs task identity')
    for task in x['tasks']:
        require(task['status'] in {'TODO', 'RUNNING', 'REVIEW', 'MERGED', 'BLOCKED', 'PAUSED'}, 'invalid task state')
        strings(task['goal_ids']); strings(task['dependencies']); strings(task['acceptance']); strings(task['attempts'])
        require(set(task['goal_ids']) <= goal_ids and set(task['dependencies']) <= goal_ids, 'unknown task goal/dependency')
        strings(task['lean_declarations'])
        if task['build_evidence']:
            validate_build(task['build_evidence'])
        require(task['platform_task_id'] or task['task_url'] or task['status'] == 'TODO', 'active task needs platform identity')
        if task['status'] != 'TODO':
            require(sha(task['base_commit']) and task['branch'], 'task needs branch and base_commit')
        if task['checkpoint_commit']:
            require(sha(task['checkpoint_commit']), 'invalid checkpoint SHA')
        if task['status'] == 'MERGED':
            direct_main = task.get('integration_mode') == 'direct-main' and task['branch'] == 'main'
            require(sha(task.get('merge_commit')) and (direct_main or https_url(task['pr_url'])),
                    'integrated task needs a commit and either direct-main or PR evidence')
    if current:
        task = next(t for t in x['tasks'] if t['id'] == current)
        if x['execution']['state'] in {'RUNNING', 'REVIEW'}:
            require(task['status'] == x['execution']['state'], 'execution/task state mismatch')
    for m in x['milestones']:
        require(m['status'] in {'TODO', 'IN_PROGRESS', 'VERIFIED', 'BLOCKED'}, 'invalid milestone')
        if m['status'] == 'VERIFIED':
            require(sha(m['evidence_commit']), 'verified milestone needs SHA')
    for c in x['claims'] + coverage['results']:
        validate_proof(c)
        require(c['milestone'] in mids, 'unknown milestone')
    for c in x['claims']:
        require(set(c['dependencies']) <= cids and c['id'] not in c['dependencies'], 'invalid claim dependency')
    for c in coverage['results']:
        require(c['scope'] == 'PAPER', 'coverage rows describe original paper targets')
        require(set(c['claim_ids']) <= cids, 'unknown coverage work item')
        require(isinstance(c['pdf_page'], int) and 1 <= c['pdf_page'] <= 44, 'invalid PDF page')
    for s in x['schedules']:
        require(s['id'] and s['timezone'] == 'Asia/Shanghai' and s['destination'], 'saved schedule needs actual identity/timezone/destination')
    validate_build(x['verification']['latest_build'])
    last = x['verification']['last_successful_build']
    if last:
        validate_build(last)
        require(last['status'] == 'PASS', 'stable build must be successful')
    for e in x['events']:
        timestamp(e['at'])
        text(e.get('public_summary'))
    return True


def validate_source(x, coverage):
    raw = (ROOT / 'paper/main.tex').read_bytes()
    require(hashlib.sha256(raw).hexdigest() == coverage['source_tex_sha256'], 'TeX changed: update source mapping explicitly')
    require(hashlib.sha256((ROOT / 'paper/paper.pdf').read_bytes()).hexdigest() == x['project']['source_paper_sha256'], 'PDF source hash mismatch')
    labels = re.findall(r'\\begin\{(?:theorem|lemma|proposition|corollary)\}\\label\{([^}]+)\}', raw.decode())
    require(set(labels) == {r['paper_label'] for r in coverage['results']}, 'named paper result coverage mismatch')


def public_status(x, coverage):
    allowed = set(x['dashboard']['approved_urls'])

    def link(value):
        return value if https_url(value) and value in allowed else None

    def build(b):
        if not b:
            return None
        return {**{k: text(b[k]) for k in ('status', 'checked_sha', 'finished_at', 'lean_version', 'mathlib_commit')}, 'source': b.get('source', 'github'), 'targets': strings(b['targets']), 'ci_url': link(b['ci_url'])}

    def proof(c):
        review = c['semantic_review']
        return {**{k: text(c[k]) for k in ('id', 'milestone', 'scope', 'verification_status', 'declaration_version', 'blocker')}, 'lean_declarations': strings(c['lean_declarations']), 'extra_hypotheses': strings(c['extra_hypotheses']), 'paper_complete': complete(c), 'build_evidence': build(c['build_evidence']), 'review_url': link(review['review_ref']) if review else None, 'reviewed_at': text(review['reviewed_at']) if review else None, 'review_recorded': bool(review)}

    current = next((t for t in x['tasks'] if t['id'] == x['execution']['current_task_id']), None)
    return {
        'schema_version': 2,
        'project': {'name': text(x['project']['name']), 'manuscript': text(x['project']['manuscript'])},
        'snapshot': {k: text(x['snapshot'][k]) for k in ('synced_at', 'source_commit', 'mode')},
        'execution': {**{k: text(x['execution'][k]) for k in ('state', 'supervisor_checked_at', 'next_action', 'blocker')}, 'task_title': text(current['title']) if current else None, 'pr_url': link(current['pr_url']) if current else None},
        'verification': {k: build(x['verification'][k]) for k in ('latest_build', 'last_successful_build')},
        'milestones': [{k: text(m[k]) for k in ('id', 'title', 'description', 'status', 'evidence_commit', 'blocker')} for m in x['milestones']],
        'claims': [{**proof(c), 'title': text(c['title']), 'paper_ref': text(c['paper_ref']), 'paper_labels': strings(c['paper_labels']), 'dependencies': strings(c['dependencies']), 'pr_url': link(c['pr_url'])} for c in x['claims']],
        'coverage': [{**proof(c), 'paper_result': text(c['paper_result']), 'paper_label': text(c['paper_label']), 'pdf_page': c['pdf_page'], 'claim_ids': strings(c['claim_ids'])} for c in coverage['results']],
        'events': [{'at': text(e['at']), 'summary': text(e['public_summary']), 'url': link(e.get('url'))} for e in x['events'] if e.get('public_summary')],
    }


def overlay_ci(x, result, expected_sha, expected_ci_url=None):
    require(result.get('source', 'github') == 'github', 'CI overlay needs remote evidence')
    require(sha(expected_sha) and result['checked_sha'] == expected_sha, 'CI result does not match checked-out snapshot source')
    validate_build(result)
    require(result['status'] in {'PASS', 'FAIL', 'CANCELLED'}, 'CI overlay must be completed')
    x = copy.deepcopy(x)
    if expected_ci_url is not None:
        # Only the exact current run supplied by the workflow is authorized.
        # A result file cannot approve its own URL or arbitrary nested links.
        repository_url = x['project']['repository_url']
        require(https_url(repository_url), 'Current CI URL requires a configured HTTPS repository')
        prefix = repository_url + '/actions/runs/'
        require(https_url(expected_ci_url) and expected_ci_url.startswith(prefix)
                and re.fullmatch(r'[1-9][0-9]*/attempts/[1-9][0-9]*', expected_ci_url[len(prefix):]),
                'Expected CI URL must identify a run attempt in this repository')
        require(result['ci_url'] == expected_ci_url, 'CI result does not match current workflow run URL')
        if expected_ci_url not in x['dashboard']['approved_urls']:
            x['dashboard']['approved_urls'].append(expected_ci_url)
    x['verification']['latest_build'] = result
    if result['status'] == 'PASS':
        x['verification']['last_successful_build'] = result
    x['snapshot'] = {'source_commit': expected_sha, 'synced_at': datetime.now(timezone.utc).isoformat(), 'mode': 'CI_SNAPSHOT'}
    return x


def coverage_markdown(coverage):
    out = '# 论文结果覆盖表\n\n此表按原 TeX 的具名 theorem/lemma/proposition/corollary 登记，共 26 项。机器来源是 `state/paper_coverage.json`，本表由 `tools/update_dashboard.py` 同步生成。页码是原 PDF 页码，TeX 行号仅辅助定位，label 为稳定定位。\n\n初始 19 项工作目标只映射其中 15 项结果，其余 11 项保留待分解。一个结果可以对应多个 Lean 声明；同一正文结果在附录证明不重复计数。Section 8 实验复现不在形式化计数内。\n\n| ID | 原文结果 | 标签 | PDF 页 / TeX 行 | 阶段 | 初始目标 | Lean 声明 |\n| --- | --- | --- | --- | --- | --- | --- |\n'
    for c in coverage['results']:
        out += f"| {c['id']} | {c['paper_result']} | `{c['paper_label']}` | {c['pdf_page']} / {c['tex_line']} | {c['milestone']} | {', '.join(c['claim_ids']) or '待分解'} | {', '.join(c['lean_declarations']) or '待建立'} |\n"
    return out


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--ci-result', type=Path)
    parser.add_argument('--expected-sha')
    parser.add_argument('--expected-ci-url')
    args = parser.parse_args()
    x = json.loads((ROOT / 'state/progress.json').read_text())
    coverage = json.loads((ROOT / 'state/paper_coverage.json').read_text())
    if args.ci_result:
        x = overlay_ci(x, json.loads(args.ci_result.read_text()), args.expected_sha, args.expected_ci_url)
    validate(x, coverage)
    validate_source(x, coverage)
    payload = json.dumps(public_status(x, coverage), ensure_ascii=False, separators=(',', ':')).replace('<', '\\u003c').replace('\u2028', '\\u2028').replace('\u2029', '\\u2029')
    outputs = {ROOT / 'docs/data.js': 'window.LEAN_TRANSFER_STATUS = ' + payload + ';\n', ROOT / 'governance/PAPER_COVERAGE.md': coverage_markdown(coverage)}
    for path, content in outputs.items():
        if args.check:
            require(path.exists() and path.read_text() == content, f'{path.name} out of sync; regenerate')
        else:
            path.write_text(content)
    print('State/coverage consistent; display projection ' + ('matches.' if args.check else 'generated.'))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError) as exc:
        sys.exit(f'Invalid state: {exc}')
