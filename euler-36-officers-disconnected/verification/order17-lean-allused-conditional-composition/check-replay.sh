#!/bin/bash
set -eu
here=$(cd -- "$(dirname -- "$0")" && pwd)
export LEAN_PATH="$here${LEAN_PATH:+:$LEAN_PATH}"
exec "${LEAN_BIN:-lean}" -j1 "$@"
