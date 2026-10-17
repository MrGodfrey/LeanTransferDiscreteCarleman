# Website prototype

This is an actual self-contained HTML/CSS/JS dashboard, **not a deployed URL**. Open `docs/index.html` locally for preview. No browser authentication, network APIs, or JavaScript framework are needed.

Data are generated from `state/progress.json` with `python3 tools/update_dashboard.py`. Do not manually edit `docs/data.js`. GitHub Actions can redeploy this snapshot whenever the main branch changes (after manually enabling Pages and ensuring the source is safe to publish).

The default state records zero verified proofs because the project has not started, but does **not** record zero token expenditure: token usage is explicitly unknown.

Before changing a private research repository to a public dashboard, inspect the generated JavaScript for potential metadata leakage. A private GitHub source repo **does not by itself guarantee a private Pages website**.
