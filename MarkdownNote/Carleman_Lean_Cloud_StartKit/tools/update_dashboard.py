#!/usr/bin/env python3
"""Validate machine-readable proof progress and publish only whitelisted fields to docs/data.js."""
import argparse
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
STATES = {"IDLE", "RUNNING", "PAUSED_LIMIT", "PAUSED_APPROVAL", "PAUSED_BLOCKER", "PAUSED_MANUAL"}
MILESTONE = {"TODO", "IN_PROGRESS", "VERIFIED", "BLOCKED"}
CLAIM = {"PLANNED", "SPECIFIED", "CONDITIONAL", "PROVEN", "AUDITED"}
BUILD = {"NOT_RUN", "PASS", "FAIL", "RUNNING"}
BILLING = {"UNKNOWN", "NORMAL", "NEAR_LIMIT", "EXHAUSTED", "PAUSED"}
SOURCES = {"unavailable", "official_ui_manual", "agent_api_report", "cli_status"}

def validate(x):
    assert x["schema_version"] == 1, "unexpected schema version"
    assert x["execution"]["state"] in STATES
    assert x["verification"]["build_status"] in BUILD
    assert x["usage"]["billing_state"] in BILLING
    assert x["usage"]["source"] in SOURCES
    assert len({m["id"] for m in x["milestones"]}) == len(x["milestones"]), 'duplicate milestones'
    assert len({c["id"] for c in x["claims"]}) == len(x["claims"]), 'duplicate claims'
    milestone_ids={m['id'] for m in x['milestones']}
    for m in x["milestones"]:
        assert m["status"] in MILESTONE
        if m["status"] == "VERIFIED":
            assert m.get("evidence_commit"), f'{m["id"]}: verified milestone needs evidence commit'
    for c in x["claims"]:
        assert c["status"] in CLAIM
        assert c["milestone"] in milestone_ids
        if c["status"] in ("PROVEN", "AUDITED"):
            assert c.get('lean_declaration') and c.get('evidence_commit'), f'{c["id"]}: missing proof evidence'
        if c["status"] == "AUDITED":
            assert c.get("audit_ref"), f'{c["id"]}: missing semantic audit reference'
    for k in ("tokens_total", "tokens_input", "tokens_output", "credits_used", "credits_remaining", "used_allowance_pct"):
        v=x['usage'].get(k)
        assert v is None or isinstance(v,(int,float)) and v>=0, f'{k}: must be null or nonnegative number'
    if x['usage']['source'] == 'unavailable':
        for k in ("tokens_total", "tokens_input", "tokens_output", "credits_used", "credits_remaining", "used_allowance_pct"):
            assert x['usage'].get(k) is None, 'unknown usage cannot contain made-up values'
    if any(x['usage'].get(k) is not None for k in ("tokens_total", "credits_used", "credits_remaining", "used_allowance_pct")):
        assert x['usage'].get('last_checked_at'), 'record source timestamp with metrics'
        assert x['usage']['source'] != 'unavailable', 'record source of usage numbers'
    if x['verification']['build_status']=='PASS':
        assert x['verification'].get('last_green_commit'), 'PASS build must name commit'
    return True

def public_status(x):
    # Strict projection: no opaque metadata, raw billing screenshots, secrets, task transcript, or manuscript text.
    return {k: x[k] for k in ('schema_version','project','execution','verification','usage','milestones','claims','events')}

def main():
    p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args()
    state=json.loads((ROOT/'state/progress.json').read_text(encoding='utf-8'))
    validate(state)
    out='window.LEAN_TRANSFER_STATUS = '+json.dumps(public_status(state), ensure_ascii=False,separators=(',', ':'))+';\n'
    path=ROOT/'docs/data.js'
    if args.check:
        if not path.exists() or path.read_text(encoding='utf-8')!=out:
            print('docs/data.js out of sync; run python3 tools/update_dashboard.py',file=sys.stderr)
            sys.exit(1)
        print('State valid; generated dashboard data matches.')
        return
    path.write_text(out,encoding='utf-8')
    print(f'Validated {len(state["claims"])} claims, {len(state["milestones"])} milestones; generated {path}.')

if __name__=='__main__': main()
