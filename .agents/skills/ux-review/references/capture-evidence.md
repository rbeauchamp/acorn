# Inspect the rendered change

Use the viewer built from the reviewed checkout. Unless the change's intent
states the owner's authorization for a run of the viewer with the core, serve it
only by the recipe that the Test instructions of `.no-mistakes.yaml` give under
"Driving the viewer": from an explicitly stopped state, with a child command
that cannot be a core. That recipe steps no learner and shows the page's text,
layout, controls and stopped lifecycle, and in a viewer started by it, and in no
other, the page's Start button may be pressed, which shows the lifecycle and its
handling of a failed child. Inspect the affected panels, controls and lifecycle
states against `docs/viewer-ux.md`. For layout changes, check the applicable
wide/compact geometries; for data changes, inspect the relevant populated and
missing/fault states. A state that only a core supplies is a run of the agent,
and a map or panel filled from a map or checkpoint that an earlier run of a
learner left is an artifact of that run: inspect either only when the owner's
authorization for it is stated in the change's intent
([running a program](../../../../CONTRIBUTING.md#running-a-program)), and
otherwise disclose the state as not inspected. There is no mandatory capture
bundle for an unrelated copy or code change.

Use supported browser tools. Read DOM values/styles alongside pixels when they
resolve the question. Derive contrast from actual colors and inspect font sizes,
timers and redraw behavior where relevant; do not infer these from screenshots.
If using headless Chrome, use a wall-clock timeout rather than virtual time:
the live SSE connection does not idle.

Keep only captures that help the current review or explain a PR finding.
Recheck changed rendering after a repair; do not repeat unaffected captures.
Successful scratch is disposable. Existing maintained viewer screenshots are
updated only when their depicted surface changes.
