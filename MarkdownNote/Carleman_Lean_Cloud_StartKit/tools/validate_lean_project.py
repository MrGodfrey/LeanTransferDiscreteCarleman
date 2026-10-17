#!/usr/bin/env python3
"""Fail closed until bootstrap creates the pinned Lean project."""
import json
from pathlib import Path
import re
import sys


def validate_project(root):
    root = Path(root)
    for name in ('lean-toolchain', 'lake-manifest.json', 'Carleman.lean'):
        if not (root / name).is_file():
            raise ValueError(f'M0a incomplete: missing {name}')
    if not any((root / name).is_file() for name in ('lakefile.lean', 'lakefile.toml')):
        raise ValueError('M0a incomplete: missing Lake configuration')
    toolchain = (root / 'lean-toolchain').read_text().strip()
    if not re.fullmatch(r'leanprover/lean4:v\d+\.\d+\.\d+(?:-rc\d+)?', toolchain):
        raise ValueError('Pin a concrete Lean release; no stable/latest/nightly alias')
    packages = json.loads((root / 'lake-manifest.json').read_text())['packages']
    mathlib = next((p for p in packages if p['name'] == 'mathlib'), None)
    if not mathlib or not re.fullmatch(r'[0-9a-f]{40}', mathlib.get('rev', '')):
        raise ValueError('Lock mathlib to a full commit in lake-manifest.json')
    if not re.search(r'^\s*import\s+Carleman\.', (root / 'Carleman.lean').read_text(), re.M):
        raise ValueError('Carleman.lean must import actual project proof modules')
    return mathlib['rev']


if __name__ == '__main__':
    try:
        print(validate_project(Path.cwd()))
    except (ValueError, KeyError) as exc:
        sys.exit(str(exc))
