#!/bin/bash
# The pinned Lean toolchain owns dependency admission and Lake invocation.
set -euo pipefail
cd "$(dirname "$0")/../lean"
exec lean -DwarningAsError=true -DautoImplicit=false --run Bootstrap.lean "$@"
