#!/usr/bin/env bash
# Run with Lean 4.36.0 and the repository's Mathlib in LEAN_PATH.
set -euo pipefail
here=$(cd "$(dirname "$0")"; pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
export LEAN_PATH="$work${LEAN_PATH:+:$LEAN_PATH}"
cd "$here"
sha512sum -c SHA512SUMS
cp FactoredCore.lean EulerFullContainment.lean core.cnf core.lrat "$work/"
gzip -dc original.cnf.gz > "$work/original.cnf"
printf '%s  %s\n' 00b1bf0edffac4f5008c82475f22dff03a89dae040be0b268f2d6f28a63cea38 "$work/original.cnf" | sha256sum -c -
cd "$work"
"${LEAN:-lean}" -o FactoredCore.olean "$PWD/FactoredCore.lean"
"${LEAN:-lean}" -o EulerFullContainment.olean "$PWD/EulerFullContainment.lean"
