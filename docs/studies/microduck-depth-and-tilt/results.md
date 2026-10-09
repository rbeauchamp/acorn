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
| (b) Tilt, forward walk | frames upright under the present bound | 949 of 949 | the bound stays; no open point |
| (b) Tilt, turn left | frames upright under the present bound | 950 of 950 | as above |
| (b) Tilt, turn right | frames upright under the present bound | 948 of 948 | as above |

- **(a)** The approach reached a near frame, and the body rested 60 s in front of the
  apartment's wall: in every one of the 806 depth frames of the rest phase a zone of the two top
  rows held a valid return, the nearest of them between 196 and 213 mm, so every frame was near
  and none was clear. No top zone went from a valid return under 300 mm to the status 255 and
  back. By the decision rule the test of a clear reading stays as it is: in the simulator a
  zone's status is 255 only when its ray meets nothing within 4 m (derivation 1 of the
  protocol), and at this pose no ray crossed an edge. What a physical sensor does stays open.
- **(b)** In each phase, from 1 s after its start, every state frame was upright under the
  present bound and under the next level's. The upward component of gravity stayed between
  -1.0000 and -0.9973 during the forward walk, -0.9964 during the left turn and -0.9972 during
  the right turn: the trunk tilted by at most 4.9 degrees, against the 14.65 degrees that the
  present bound allows. By the decision rule the bound stays (derivation 2 had already ruled
  out the next level), and issue 95 gets no open point: the present bound holds the walking and
  turning body upright in this run.

The phases did what they were meant to: during the forward phase the odometry moved 2.41 m with
the policy reading walk in every frame, the left turn turned 17.2 rad and the right turn 20.6
rad, no frame reported a fall, the trunk stayed at 0.111 m or higher, and the daemon accepted
every command (592 in session T, 27 in session D). These checks were read from the same records
after the analysis and decide nothing.

## Scope

One body, one bare floor and one apartment pose, one minute of each phase, on one machine under
the load of the fleet's other jobs at the time; a scripted walk at 0.3 m/s and turns at 1.5
rad/s, which are the action table's magnitudes, not a learning agent's sequence of actions,
skills or falls. The counts are observations of this run and not bounds. Nothing here describes
the physical robot or its sensor.

## Records

The record of session T, 19.2 MB as written and 5.6 MB compressed, is over the protocol's limit
of 2 MB, so the task keeps it outside the repository and the repository holds its SHA-256 and
[an extract](observations/r1/session-T-extract.tsv) with the clock, the phase and the upward
component of each state frame, as the protocol fixes. Rerunning the analysis's tilt part on the
extract gives the same counts and extremes.

## Deviation from the protocol

The protocol has the records committed compressed with gzip. The repository's corpus audit
refuses archives, so the record of session D (561 KB) and the vendor script's output are
committed uncompressed, byte for byte; their hashes in the [manifest](observations/r1/manifest-sha256.txt)
are those of the records as written. Nothing else of the run departs from the protocol.
