# Inspect the rendered change

Use the viewer built from the reviewed checkout, served only by the recipe that
the Test instructions of `.no-mistakes.yaml` give under "Driving the viewer":
from an explicitly stopped state, with a child command that cannot be a core.
That recipe steps no learner and shows the page's text, layout, controls and
stopped lifecycle, and in a viewer started by it, and in no other, the page's
Start button may be pressed, which shows the lifecycle and its handling of a
failed child. Open the page in a clean browser profile (or inspect HTML/SVG/CSS/BMP
responses directly): the viewer is pure zero-JS server-rendered HTML with strict
`Content-Security-Policy` (`script-src 'none'`) and holds no client storage.
One sentence on authorization governs the directions here on starting the viewer
with a core and on the states that such a run supplies: each only and each never
about them binds a review whose change's intent states no authorization for that
run, and where the intent states the owner's authorization
([running a program](../../../../CONTRIBUTING.md#running-a-program)), exactly
what that authorization names or points to may be started and the states it
supplies inspected, and nothing wider.
It reaches no other rule of the review. Inspect the affected panels, controls
and lifecycle states against `docs/viewer-ux.md`. For layout changes, check the
applicable wide/compact geometries; for data changes, inspect the relevant
populated and missing/fault states. A state that only a core supplies needs a
start that is not on the closed list: disclose it as not inspected. There is no mandatory capture bundle
for an unrelated copy or code change.

Use supported browser tools. Read DOM values/styles alongside pixels when they
resolve the question. Derive contrast from actual colors and inspect font sizes,
refresh/stream cadence and redraw behavior where relevant; do not infer these from screenshots.
If using headless Chrome, note that `?stream=1` keeps `/stream/stage.bmp` open
(`multipart/x-mixed-replace`), so use a wall-clock timeout rather than virtual time
when inspecting stream mode.

Keep only captures that help the current review or explain a PR finding.
Recheck changed rendering after a repair; do not repeat unaffected captures.
Successful scratch is disposable. Existing maintained viewer screenshots are
updated only when their depicted surface changes.
