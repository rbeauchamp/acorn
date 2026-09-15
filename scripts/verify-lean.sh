#!/bin/bash
# Offline ordinary Lean checks; the complete merge suite is scripts/verify.sh.
set -euo pipefail
cd "$(dirname "$0")/.."
exec ./scripts/lean.sh exe acorn-gates "$@"
