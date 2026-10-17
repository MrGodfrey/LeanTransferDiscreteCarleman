# Cloud environment setup

Use the existing `/workspace/LeanTransferDiscreteCarleman` checkout. Cloud tasks
are isolated; do not create a Git worktree unless the user explicitly requests it.
Inspect the current branch, full HEAD, status, and root `AGENTS.md` first.

The prepared image uses Python 3.12 and Node 24; GitHub CI uses Python 3.12 and
Node 22. No Python or npm packages, daemon, database, or application secrets are
required. GitHub authentication comes from the existing platform connection.

```bash
cd /workspace/LeanTransferDiscreteCarleman
export ELAN_HOME=/workspace/.carleman-environment/elan
export PATH="$ELAN_HOME/bin:$PATH"
bash tools/setup_lean.sh
bash tools/lean_ci.sh
python3 -m unittest discover -s tools -p 'test_*.py'
node --test tools/test_dashboard.js
python3 tools/update_dashboard.py --check
```

Lean is pinned to `leanprover/lean4:v4.35.0`; mathlib is pinned to
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Preserve the checked-in manifest.
The setup script accepts additional mathlib cache roots as arguments.
Only the required import closure is fetched; the initial build used 719 Lake
jobs with prebuilt mathlib outputs. Inspect CPU, memory, and disk before deciding
to build much larger uncached dependency trees.

Required network destinations are GitHub and its source/release asset hosts,
`release.lean-lang.org` (Elan release metadata), `releases.lean-lang.org`,
`cache.mathlib.org` (mathlib cache), and `lakecache.blob.core.windows.net`
(official legacy cache endpoint). `api.github.com` is needed for PR/CI operations.
Never disable TLS or checksum verification. Missing API administration permissions
are separate from ordinary Git access.

The initial cloud installation used the official GitHub Lean archive while the
Elan metadata domain was unavailable. Its published SHA-256 was verified:
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`
for `lean-4.35.0-linux.tar.zst`. Elan links the extracted official toolchain;
there is no floating project override. Standard restoration on a clean machine
uses `tools/setup_lean.sh` and Elan's normal pinned-toolchain installation.

No live process needs restoring. Elan/toolchains and `.lake` outputs are reusable
filesystem state, not proof evidence. A published snapshot and successful fresh
task restoration must each be verified independently. Environment draft saving
does not establish either. Do not start the long-running proof loop during setup.
