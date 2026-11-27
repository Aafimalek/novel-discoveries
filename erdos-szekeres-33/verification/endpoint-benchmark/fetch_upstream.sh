#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
REV=61bfbd6f04d73865a5037b0a416d5ba18ce34fbd
mkdir -p upstream/lib
for f in erdos.py sat.py; do
  curl -fsSL "https://raw.githubusercontent.com/jcpaik/erdos-szekeres-sat/$REV/lib/$f" -o "upstream/lib/$f"
done
sha256sum -c <<'EOF_HASH'
75e592e1f0f037803a22a47397b986865140be23ce9f2aa430b53929dedb3732  upstream/lib/erdos.py
55da4d770790811e2baf5a4d275f1d4360b2b7db7db4394c568041173fef09a8  upstream/lib/sat.py
EOF_HASH
