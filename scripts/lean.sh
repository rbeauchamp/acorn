#!/bin/bash
# The pinned Lean toolchain owns dependency admission and Lake invocation.
# `exe NAME ARGS` runs the Acorn program NAME. In work on a change, only an
# invocation on the closed list in the Test instructions of .no-mistakes.yaml is
# run without the owner's authorization (CONTRIBUTING.md, "Running a program").
set -euo pipefail
cd "$(dirname "$0")/../lean"
exec lean -DwarningAsError=true -DautoImplicit=false --run Bootstrap.lean "$@"
