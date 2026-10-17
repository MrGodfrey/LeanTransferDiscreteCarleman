#!/usr/bin/env python3
"""Record the CI step outcomes; runs on the checkout actually checked by this run."""
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess

out = Path('.ci')
out.mkdir(exist_ok=True)
read = lambda p: p.read_text().strip() if p.exists() else None
outcome = os.environ['BUILD_OUTCOME']
status = 'PASS' if outcome == 'success' and os.environ['SETUP_OUTCOME'] == 'success' else 'CANCELLED' if outcome == 'cancelled' else 'FAIL'
result = {
    'status': status,
    'checked_sha': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
    'ci_url': f"{os.environ['GITHUB_SERVER_URL']}/{os.environ['GITHUB_REPOSITORY']}/actions/runs/{os.environ['GITHUB_RUN_ID']}/attempts/{os.environ['GITHUB_RUN_ATTEMPT']}",
    'finished_at': datetime.now(timezone.utc).isoformat(),
    'lean_version': read(out / 'lean-version.txt'),
    'mathlib_commit': read(out / 'mathlib-commit.txt'),
    'targets': ['Carleman'],
    'source_head_sha': os.environ.get('SOURCE_HEAD_SHA') or None,
}
(out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
print(f"Recorded {status} for {result['checked_sha']}")
