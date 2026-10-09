# Depth dropout at rest and trunk tilt while walking, in the Microduck simulator: protocol

This is the protocol of study microduck-depth-and-tilt, the first measurement of
[issue 95](https://github.com/rbeauchamp/acorn/issues/95) (increment 6). It fixes every
choice below before any observation of the study exists.

**Protocol revision 1. Status when written: not run.** It is registered by the signed commit
that adds this file, made before any run of the study; the record of the run names that
commit. A change after registration is a new revision with a new number. The owner's standing
approval of every run of the vendor's simulator (2026-10-08, relayed by Firstmate) is the
authorization that the [scientific evidence guidance](../../../CONTRIBUTING.md#scientific-evidence)
requires; it is not an approval of this design.

## Questions

The goal of the Microduck world gives its event at a near reading while its latch is armed,
and a clear reading arms the latch ([design](../../design.md#an-embodied-world-the-microduck)). Two of its
choices rest on behaviour that no record shows.

- **(a) Dropout.** A clear reading has, in every zone of the two top rows of the depth frame,
  the status 255 or a valid return of at least 400 mm (`Acorn.Handcrafted.Microduck.distant`). If the status of a zone in
  front of an obstacle dropped to 255 and came back, two events could follow with no retreat.
  Does a clear reading occur between two near readings while the body rests near an
  obstacle, so that a clear reading should require a valid return of at least 400 mm in every
  top zone?
- **(b) Tilt.** A near or clear reading needs an upright trunk: the gravity word for the
  upward component below the level of -0.95 (`Acorn.Handcrafted.Microduck.upright_iff`). How often is the trunk upright
  while the body walks forward and while it turns, and does the bound have to move to the
  next level of the gravity word?

## What derivation settles

Claim labels follow the [baseline assessment](../../baseline-assessment.md): machine-checked,
argued, assumed and UNKNOWN.

1. **The simulator's status of a zone.** *Argued from the vendor's source.* The simulated
   sensor (microduck_rl at commit 1f2e4afcf33fbc75172b893c82fb66da9e3fc7ea, file
   src/mjlab_microduck/sim/tof.py) casts one ray for each zone from the sensor's site, at the
   centre of the zone. A zone has the status 5 and the measured distance when the ray meets
   geometry within 4 m, and the status 255 and the distance 0 otherwise, or for every zone
   before the simulation's first forward pass. The noise, a normal deviate of 3 mm plus 20 mm
   for each 4 m of range, changes the distance only, never the status. So in the simulator a
   zone that held a valid return reports 255 only when its ray no longer meets geometry within
   4 m: an edge of the obstacle crossed by a ray as the body sways, not a failure of the
   sensor. A clear reading between two near readings at rest needs every one of the sixteen
   top rays to leave the obstacle or to stay at least 400 mm from it while the body does not
   move away. Nothing here says what a physical sensor does; that is out of scope (issue 95).
2. **The bound of an upright trunk.** *Argued from the record's geometry, as the design's
   argument that a flat floor is not read as near.* A conversion of the daemon's decimal to a
   word rounds to the nearest thousandth, at a tie away from zero, so the word is below -967
   exactly when the upward component is at most -0.9675, and below the next level's bound,
   -867, exactly when it is at most -0.8675 (`Acorn.Handcrafted.Microduck.upright_iff`, and the same count of levels). An
   upright trunk is tilted by less than 14.65 degrees; at the next level by less than 29.83
   degrees. The design's argument bounds the lowest beam of the two top rows at 4.1 degrees
   below the horizontal at rest, so at the next level a beam points at most 33.9 degrees below
   it, and a flat floor is returned at more than 1.79 times the height of the sensor. In the
   least favourable direction the sensor, 0.082 m forward, 0.021 m to the left and 0.113 m up
   from the origin of the trunk, is then 55.8 mm above that origin: 171.8 mm above the floor
   for a standing body (origin at 0.116 m) and 116.8 mm for a sitting one (origin at 0.061 m).
   The floor is then returned at more than 307 mm for a standing body and more than 209 mm for
   a sitting one. **So at the next level a flat floor can be read as near by a sitting body,
   and a standing body keeps 7 mm of margin over 300 mm, about one and a half deviations of the
   simulated noise at that range.** The bound cannot move to the next level without a further
   condition on the near test. This settles question (b)'s second part before any run: the
   bound does not move in this study. The run measures only how often the walking body is
   upright under the present bound.

## Design

Two sessions of the vendor's simulator, each started and stopped by the vendor's script, with
the installation of the execution section. A session program (in the execution section)
connects to the daemons' sockets directly, subscribes, enables the policy, sends the same
command lines that microduck-host sends for its actions (robot.move with vx 0.3, or vyaw 1.5
or -1.5, and the other two components 0.0), resends a velocity every 100 ms while a phase
commands it, and records every frame of the subscribed streams with the phase it arrived in.

- **Session T (tilt), bare floor (the vendor's default scene).** Phases after robot.enable:
  stand 10 s (no command); rest 5 s; forward 20 s; pause 3 s; left 20 s; pause 3 s; right
  20 s; pause 3 s. Records the state stream.
- **Session D (depth), apartment scene.** Phases after robot.enable: stand 10 s; approach,
  forward until a depth frame has a valid return under 300 mm in a top zone, at most 15 s;
  settle 2 s (no command; the daemon zeroes the velocity 500 ms after the last send); rest
  60 s (no command). Records the depth stream. The vendor's record shows the
  body starting in front of a wall whose top zones read 540 to 560 mm.

## Estimands

- **(a)** In the rest phase of session D, counting only depth frames: a frame is *near* when
  a top zone has the status 5 and a distance under 300 (the depth part of `Acorn.Handcrafted.Microduck.near`), and *clear*
  when every top zone has the status 255, or the status 5 and a distance of at least 400 (the
  depth part of `Acorn.Handcrafted.Microduck.clear`). The estimand is the number of clear frames that lie after one near
  frame and before another. It leaves out the upright and freshness parts of both tests,
  which can only make fewer frames near or clear, so it counts at least every re-arming
  between two near readings that the goal would see. Descriptive only: for each top zone, the
  number of times it goes from a valid return under 300 to 255 and back to a valid return.
- **(b)** In each of the phases forward, left and right of session T, from 1 s after the
  phase starts to its end: the number of state frames, the fraction whose upward component
  is at most -0.9675 (upright under the present bound), the fraction at most -0.8675 (upright
  at the next level), and the least, the median and the greatest upward component.

## Decision rules, fixed now

- **(a)** If the estimand is at least 1, a clear reading is changed to require, in every top
  zone, the status 5 and a valid return of at least 400 mm (the 255 branch of `Acorn.Handcrafted.Microduck.distant` is
  removed), with the theorems and the contract `Acorn.Decisions.microduck_clear` restated. If it is 0, the
  test stays as it is, and the record says that the simulator's status cannot drop out
  (derivation 1) and that the physical sensor's remains open. If the approach phase ends
  without a near frame, (a) is inconclusive and nothing changes.
- **(b)** The bound stays (derivation 2). If the upright fraction under the present bound is
  under one half in the forward phase or in either turn, issue 95 gets an open point: the goal
  rarely decides near or clear while the body walks, and a redesign of the upright test with a
  condition on the trunk's height is the candidate. Otherwise the record says that the
  present bound holds the walking body upright most of the time. No code changes for (b).

## Uncertainty, stopping and failures

One session of each kind, one run. Frames are autocorrelated within a phase, so no interval is
given; the counts and fractions are observations of this run, not bounds. The run stops at the
end of session D. A session that fails to start (a daemon that does not answer its
subscription or robot.enable within 15 s) is repeated once after down and up; a second failure
ends the study as a negative result with its cause recorded. A frame that does not parse is
counted and left out.

## Resource budget

The installation (about 5 GB of disk in a scratch root inside the worktree, about 2 minutes of
build at two jobs), about 90 s for session T and 90 s for session D with start and stop, under
the build slot that Firstmate grants. Nothing is left running, no cache of the home directory
is written, and the scratch root is removed after the records are copied.

## Execution

From the checkout root, each block extracted verbatim and run with bash. The scratch root and
the environment:

```bash
export S="$PWD/.scratch/duck-sim"
export HOME="$S/home" RUSTUP_HOME="$S/rustup" CARGO_HOME="$S/cargo" UV_CACHE_DIR="$S/uv"
export HF_HOME="$S/hf" XDG_CACHE_HOME="$S/xdg" MPLCONFIGDIR="$S/mpl" CARGO_BUILD_JOBS=2
export RUSTUP_TOOLCHAIN=1.99.0 DUCK_SIM_RL="$S/src/microduck_rl" DUCK_SIM_STATE="$S/st"
export DUCK_SIM_VIEWER=0
export PATH="$S/bin:/Users/richard/.cargo/bin:/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin"
```

The installation, at the pinned commits:

```bash
set -euo pipefail
mkdir -p "$S"/home "$S"/bin "$S"/src "$S"/st "$S"/uv "$S"/hf "$S"/xdg "$S"/mpl
printf '#!/bin/sh\necho "sudo refused in the scratch environment" >&2\nexit 1\n' > "$S/bin/sudo"
chmod +x "$S/bin/sudo"
fetch() {
  git init -q "$2"; git -C "$2" remote add origin "$1"
  git -C "$2" fetch -q --depth 1 origin "$3"; git -C "$2" checkout -q FETCH_HEAD
  test "$(git -C "$2" rev-parse HEAD)" = "$3"
}
fetch https://github.com/pollen-robotics/microduck.git "$S/src/microduck" 9136aa4ee88e81edf2bcaf3527e90b65da25f1eb
fetch https://github.com/pollen-robotics/microduck_rl.git "$S/src/microduck_rl" 1f2e4afcf33fbc75172b893c82fb66da9e3fc7ea
rustup toolchain install 1.99.0 --profile minimal --no-self-update
(cd "$S/src/microduck" && cargo build -p robotd -p robotctl -p tof -p sounds -p configd -p updater)
(cd "$S/src/microduck_rl" && uv sync --frozen)
```

The session program, written to "$S/session.py" verbatim and run with python3 -I:

```python
import json, socket, sys, time
state_sock, tof_sock, plan_name, out_path = sys.argv[1:5]
PLANS = {
    "T": [("stand", 10.0, None), ("rest", 5.0, None), ("forward", 20.0, (0.3, 0.0)),
          ("pause1", 3.0, None), ("left", 20.0, (0.0, 1.5)), ("pause2", 3.0, None),
          ("right", 20.0, (0.0, -1.5)), ("pause3", 3.0, None)],
    "D": [("stand", 10.0, None), ("approach", 15.0, (0.3, 0.0)), ("settle", 2.0, None),
          ("rest", 60.0, None)],
}
def connect(path):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM); s.connect(path); s.setblocking(False)
    return s
def line(s, text): s.sendall((text + "\n").encode())
def move(ident, vx, vyaw):
    return ('{"jsonrpc":"2.0","id":%d,"method":"robot.move","params":{"vx":%s,"vy":0.0,"vyaw":%s}}'
            % (ident, repr(vx), repr(vyaw)))
links = {"control": connect(state_sock)}
if plan_name == "T":
    links["state"] = connect(state_sock)
    line(links["state"], '{"jsonrpc":"2.0","id":0,"method":"robot.subscribe","params":{}}')
else:
    links["depth"] = connect(tof_sock)
    line(links["depth"], '{"jsonrpc":"2.0","id":1,"method":"tof.stream"}')
line(links["control"], '{"jsonrpc":"2.0","id":2,"method":"robot.enable","params":{"on":true}}')
buffers = {name: b"" for name in links}
ident = 3
out = open(out_path, "w")
def pump(phase):
    near = False
    for name, s in links.items():
        try:
            chunk = s.recv(1 << 20)
        except BlockingIOError:
            continue
        buffers[name] += chunk
        while b"\n" in buffers[name]:
            raw, buffers[name] = buffers[name].split(b"\n", 1)
            text = raw.decode()
            out.write("%d\t%s\t%s\t%s\n" % (time.monotonic_ns(), phase, name, text))
            if name == "depth" and '"tof.frame"' in text:
                p = json.loads(text)["params"]
                near = near or any(p["status"][z] == 5 and p["distance_mm"][z] < 300
                                   for z in range(16))
    return near
for phase, seconds, velocity in PLANS[plan_name]:
    out.write("%d\t%s\tphase\tstart\n" % (time.monotonic_ns(), phase))
    end = time.monotonic() + seconds
    next_send = 0.0
    while time.monotonic() < end:
        now = time.monotonic()
        if velocity is not None and now >= next_send:
            line(links["control"], move(ident, velocity[0], velocity[1])); ident += 1
            next_send = now + 0.1
        if pump(phase) and phase == "approach":
            break
        time.sleep(0.002)
out.write("%d\tend\tphase\tstart\n" % time.monotonic_ns())
out.close()
```

The two sessions, with the records in "$S/records":

```bash
set -euo pipefail
mkdir -p "$S/records"
cd "$S/src/microduck"
scripts/duck-sim > "$S/records/up-T.log" 2>&1
for _ in $(seq 1 60); do [ -S "$S/st/duck-a.sock" ] && break; sleep 0.5; done
sleep 3
python3 -I "$S/session.py" "$S/st/duck-a.sock" "$S/st/duck-a-tof.sock" T "$S/records/session-T.tsv"
scripts/duck-sim down > "$S/records/down-T.log" 2>&1
DUCK_SIM_SCENE=apartment scripts/duck-sim > "$S/records/up-D.log" 2>&1
for _ in $(seq 1 60); do [ -S "$S/st/duck-a.sock" ] && [ -S "$S/st/duck-a-tof.sock" ] && break; sleep 0.5; done
sleep 3
python3 -I "$S/session.py" "$S/st/duck-a.sock" "$S/st/duck-a-tof.sock" D "$S/records/session-D.tsv"
scripts/duck-sim down > "$S/records/down-D.log" 2>&1
```

## Records

The observations are the lines that the daemons sent, with the reading of the monotonic clock
at their receipt and their phase, as the session program wrote them, and the vendor script's
output. Each session record is compressed with gzip, byte for byte. A compressed record of at
most 2 MB is committed to observations/r1 beside this file; a larger one is kept by the task
outside the repository, and the repository holds its SHA-256 and an extract of the fields the
analysis reads (the clock, the phase and the upward component of each state frame), marked as
an extract. The SHA-256 manifest of every record, and an identity file naming the registering
commit, the pinned commits and the time of each session, are committed before the scratch root
is removed. The results file presents the observations; it never rewrites them.

## Analysis

Run with python3 -I on the two session records; it uses exact decimal arithmetic on the text of
each number, so the comparison with -0.9675 and -0.8675 is exact:

```python
import json, sys
from decimal import Decimal
from statistics import median
def frames(path, link, method):
    for row in open(path):
        stamp, phase, name, text = row.rstrip("\n").split("\t", 3)
        if name == link and method in text:
            try:
                yield phase, json.loads(text, parse_float=Decimal)["params"]
            except ValueError:
                print("unparsed frame in", path)
tilt, depth = sys.argv[1], sys.argv[2]
for phase in ("forward", "left", "right"):
    rows = [(p["t_ns"], p["safety"]["gravity"][2]) for ph, p in frames(tilt, "state", "robot.state") if ph == phase]
    start = rows[0][0] + 1_000_000_000
    up = [z for t, z in rows if t >= start]
    present = sum(1 for z in up if z <= Decimal("-0.9675")) / len(up)
    following = sum(1 for z in up if z <= Decimal("-0.8675")) / len(up)
    print(phase, len(up), round(present, 4), round(following, 4), min(up), median(up), max(up))
top = range(16)
def near(p): return any(p["status"][z] == 5 and p["distance_mm"][z] < 300 for z in top)
def clear(p): return all(p["status"][z] == 255 or (p["status"][z] == 5 and p["distance_mm"][z] >= 400) for z in top)
rest = [p for ph, p in frames(depth, "depth", "tof.frame") if ph == "rest"]
reached = any(near(p) for p in rest)
between, seen_near, pending = 0, False, 0
for p in rest:
    if near(p):
        if seen_near: between += pending
        seen_near, pending = True, 0
    elif clear(p) and seen_near:
        pending += 1
toggles = [0] * 16
for z in top:
    state = "none"
    for p in rest:
        valid_near = p["status"][z] == 5 and p["distance_mm"][z] < 300
        if state == "none" and valid_near: state = "near"
        elif state == "near" and p["status"][z] == 255: state = "dropped"
        elif state == "dropped" and p["status"][z] == 5:
            toggles[z] += 1; state = "near" if valid_near else "none"
print("rest frames", len(rest), "near reached", reached, "clear between near", between, "zone toggles", toggles)
```

## What a result will and will not establish

A result describes one body in one simulated scene for about a minute of each kind, under this
machine's load. It does not describe the physical robot, its sensor or its floor, or the walk
of a learning agent, whose actions differ from the scripted phases. Decision (a) changes the
goal only on evidence that the simulator re-arms the latch at rest; decision (b) changes no
code, because derivation 2 already shows the next level unsafe for a sitting body.

## Revisions

Revision 1 is this file as committed by its registering commit.
