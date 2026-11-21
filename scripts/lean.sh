#!/bin/bash
# The pinned Lean toolchain owns dependency admission and Lake invocation.
# `exe NAME` runs the Acorn program NAME, and some of those programs step the
# agent or a learner: the Test instructions of .no-mistakes.yaml say which, and
# CONTRIBUTING.md, "Running a program", gives the rule. `build` runs none.
set -euo pipefail
cd "$(dirname "$0")/../lean"
exec lean -DwarningAsError=true -DautoImplicit=false --run Bootstrap.lean "$@"
