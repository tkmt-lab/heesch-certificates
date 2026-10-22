#!/bin/sh
# Build drat-trim (Marijn Heule et al., MIT licence) at the commit used for all checks.
# Usage: sh tools/build_drat_trim.sh  ->  tools/drat-trim/drat-trim
set -eu
COMMIT=2e3b2dc0ecf938addbd779d42877b6ed69d9a985
SRC_SHA256=d834b649f437e091597f5347f259b9f681087f89ca0844d0cee250a1a1a0c2ee
DIR="$(cd "$(dirname "$0")" && pwd)/drat-trim"
if [ ! -d "$DIR/.git" ]; then
  git clone --quiet https://github.com/marijnheule/drat-trim.git "$DIR"
fi
git -C "$DIR" checkout --quiet "$COMMIT"
if command -v sha256sum >/dev/null 2>&1; then H=$(sha256sum "$DIR/drat-trim.c" | cut -d' ' -f1); else H=$(shasum -a 256 "$DIR/drat-trim.c" | cut -d' ' -f1); fi
[ "$H" = "$SRC_SHA256" ] || { echo "drat-trim.c hash mismatch: $H" >&2; exit 1; }
cc "$DIR/drat-trim.c" -std=c99 -O2 -o "$DIR/drat-trim"
echo "built $DIR/drat-trim (commit $COMMIT)"
