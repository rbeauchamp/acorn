# Inspect the rendered change

Use the viewer built from the reviewed checkout. Inspect the affected panels,
controls and lifecycle states against `docs/viewer-ux.md`. For layout changes,
check the applicable wide/compact geometries; for data changes, inspect the
relevant populated and missing/fault states. There is no mandatory capture bundle
for an unrelated copy or code change.

Use supported browser tools. Read DOM values/styles alongside pixels when they
resolve the question. Derive contrast from actual colors and inspect font sizes,
timers and redraw behavior where relevant; do not infer these from screenshots.
If using headless Chrome, use a wall-clock timeout rather than virtual time:
the live SSE connection does not idle.

Keep only captures that help the current review or explain a PR finding.
Recheck changed rendering after a repair; do not repeat unaffected captures.
Successful scratch is disposable. Existing maintained viewer screenshots are
updated only when their depicted surface changes.
