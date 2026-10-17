#!/usr/bin/env bash
set -euo pipefail
# Run at the repository root. Project versions are committed by M0a, never guessed here.
python3 tools/validate_lean_project.py
if ! command -v elan >/dev/null 2>&1 && [ ! -x "$HOME/.elan/bin/elan" ]; then
  task_installer="$(mktemp)"
  trap 'rm -f "$task_installer"' EXIT
  curl --proto '=https' --tlsv1.2 -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "$task_installer"
  bash "$task_installer" -y --default-toolchain none
fi
export PATH="$HOME/.elan/bin:$PATH"
lean --version
lake exe cache get
