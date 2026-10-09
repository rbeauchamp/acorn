# Depth dropout at rest and trunk tilt while walking, in the Microduck simulator: result

This is the result of revision 1 of study microduck-depth-and-tilt, the first measurement of
[issue 95](https://github.com/rbeauchamp/acorn/issues/95). The [protocol](protocol.md) defines
every term used here and fixed every choice before the run; its registering commit is
3c9afd7c1af770638267aacd82058e1839d06be7. The run was on 2026-10-09 from 10:51:47 to 10:55:06
UTC; the [identity file](observations/r1/identity.txt) names its inputs, and the
[manifest](observations/r1/manifest-sha256.txt) the hash of every record.

## Result

| Question | Estimand | Value | Decision |
|---|---|---|---|
| (a) Dropout at rest | clear depth frames between two near ones, at rest | 0 of 806 frames | the clear test stays |
| (b) Tilt, forward walk | frames upright under the present bound, from 1 s after the phase's first frame | 949 of 949 | the bound stays; no open point |
| (b) Tilt, turn left | frames upright under the present bound | 950 of 950 | as above |
| (b) Tilt, turn right | frames upright under the present bound | 948 of 948 | as above |

- **(a)** The approach reached a near frame, and the body rested 60 s in front of the
  apartment's wall: in every one of the 806 depth frames of the rest phase a zone of the two top
  rows held a valid return, the nearest of them between 196 and 213 mm, so every frame was near
  and none was clear. No top zone went from a valid return under 300 mm to the status 255 and
  back. By the decision rule the test of a clear reading stays as it is: in the simulator a
  zone's status is 255 only when its ray meets nothing within 4 m (derivation 1 of the
  protocol), and at this pose no ray crossed an edge. What a physical sensor does stays open.
- **(b)** In each phase, in the frames the analysis kept (from 1 s after the phase's first
  frame, see the addendum), every state frame was upright under the present bound and under
  the next level's. The upward component of gravity stayed between -1.0000 and -0.9973 during
  the forward walk, -0.9964 during the left turn and -0.9972 during the right turn: in those
  frames the trunk tilted by at most 4.9 degrees, against the 14.65 degrees that the present
  bound allows. Over the whole of each phase, its first second included, every frame was
  upright too, and the largest tilt was 5.1 degrees, in the forward phase's first second. By
  the decision rule the bound stays (derivation 2, made concrete in the addendum, rules out the
  next level), and issue 95 gets no open point: the present bound holds the walking and turning
  body upright in this run.

The phases did what they were meant to: during the forward phase the odometry moved 2.41 m with
the policy reading walk in every frame, the left turn turned 17.2 rad and the right turn 20.6
rad, no frame reported a fall, the trunk stayed at 0.111 m or higher, and the daemon accepted
every command (592 in session T, 27 in session D). These checks were read from the same records
after the analysis and decide nothing.

## Scope

One body, one bare floor and one apartment pose, 20 s of each walking and turning phase (about
19 s of each kept by the analysis) and 60 s at rest, on one machine under
the load of the fleet's other jobs at the time; a scripted walk at 0.3 m/s and turns at 1.5
rad/s, which are the action table's magnitudes, not a learning agent's sequence of actions,
skills or falls. The counts are observations of this run and not bounds. Nothing here describes
the physical robot or its sensor.

## Records

The record of session T, 19.2 MB as written and 5.6 MB compressed, is over the protocol's limit
of 2 MB, so the task keeps it outside the repository and the repository holds its SHA-256 and
[an extract](observations/r1/session-T-extract.tsv) with the clock, the phase and the upward
component of each state frame, as the protocol fixes. The protocol's analysis reads the full
record, not the extract; the reader of the extract in the addendum prints, for the three
phases, the same lines as the analysis did.

## Deviation from the protocol

The protocol has the records committed compressed with gzip. The repository's corpus audit
refuses archives, so the record of session D (561 KB) and the vendor script's output are
committed uncompressed, byte for byte; their hashes in the [manifest](observations/r1/manifest-sha256.txt)
are those of the records as written. Nothing else of the run departs from the protocol.

## Addendum, 2026-10-09, after the second reading of the change

These corrections follow an independent reading of this result. They change no observation
and no decision; revision 1 of the protocol is unchanged, and each item says where the run or
the protocol's text departs from what revision 1 states.

- **The window of the tilt analysis.** The protocol's estimand counts the frames from 1 s
  after a phase starts; its analysis program keeps the frames from 1 s after the phase's first
  state frame, by the daemon's clock. The first frame of each phase came 6.2, 3.0 and 20.1 ms
  after the phase began (forward, left, right). With the window as the estimand states it, by
  the receipt clock, the counts are 949, 951 and 949 frames, all upright: the decision is the
  same.
- **The largest tilt.** The 4.9 degrees above is the largest tilt in the frames the analysis
  kept. In the forward phase's first second the trunk reached 5.1 degrees (an upward component
  of -0.9961); every frame of every phase was upright.
- **Derivation 2, made concrete.** The protocol shows only that at the next level the
  argument that a flat floor is not read as near no longer holds for a sitting body: a lower
  bound of 209 mm on the floor's return does not by itself give a return under 300 mm. A pose
  does. A sitting body, with the origin of its trunk at 61 mm, pitched forward by 29.8 degrees
  about its own lateral axis, with the head at its rest pose (pitched 14.2 degrees down and
  rolled 2.8 degrees), has an upward component of -0.8678, so it is upright at the next level.
  Its sensor is then 118.3 mm above the floor, and the centre rays of row 1 in the two middle
  columns, which are the rays the simulator casts, point 30.0 degrees below the horizontal and
  meet a flat floor at 237 mm: near. The simulated noise at that range is about 4 mm. The pose
  rests on the design's assumptions (a flat floor, the head at rest, the origin of the trunk at
  its sitting height while it tilts); whether the body takes it is not known. A standing body
  at the same tilt meets the floor at 347 mm.
- **Durations.** The walking and turning phases lasted 20 s each, of which the analysis kept
  about 19 s; only the rest phase of session D lasted 60 s.
- **The reader of the extract.** Run with python3 -I on observations/r1/session-T-extract.tsv
  (SHA-256 of the program 437461d9fa7892c8865d812158ab8f004b429a19483f0bae978a9b808b0a64ae), it
  prints, for the three phases, the same lines as the protocol's analysis printed from the full
  record:

```python
import sys
from decimal import Decimal
from statistics import median
rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1]) if not l.startswith("#")][1:]
for phase in ("forward", "left", "right"):
    sel = [(int(t), Decimal(u)) for _, ph, t, u in rows if ph == phase]
    start = sel[0][0] + 1_000_000_000
    up = [u for t, u in sel if t >= start]
    present = sum(1 for z in up if z <= Decimal("-0.9675")) / len(up)
    following = sum(1 for z in up if z <= Decimal("-0.8675")) / len(up)
    print(phase, len(up), round(present, 4), round(following, 4), min(up), median(up), max(up))
```
