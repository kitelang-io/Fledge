#!/usr/bin/env zsh
# Reseed a Kite checkout's bootstrap binary from its current compiler sources.
#
# This is the one job Fledge performed for the Kite repo: compile the Kite
# compiler-in-Kite down to a native executable and install it as the committed
# seed (bootstrap/kite-seed). The self-hosted compiler bootstraps from that seed
# thereafter, so Fledge is only needed when a parser-level change makes the
# existing seed unable to compile the sources.
#
# Point KITE_ROOT at a Kite checkout (default: a sibling ../Language).
set -e

# Make the OCaml toolchain (dune) discoverable when opam manages it, without
# assuming a particular install prefix. Falls back to the inherited PATH.
command -v opam >/dev/null 2>&1 && eval "$(opam env 2>/dev/null)" || true

HERE=${0:A:h}
KITE_ROOT=${KITE_ROOT:-"$HERE/../Language"}
[ -d "$KITE_ROOT/compiler" ] || { echo "no Kite checkout at $KITE_ROOT (set KITE_ROOT)"; exit 1; }

echo "building Fledge ..."
dune build --root "$HERE"

echo "reseeding via Fledge ..."
cd "$KITE_ROOT"
dune exec --root "$HERE" bin/main.exe -- exe \
  compiler/frontend/kfront.kite compiler/codegen/codegen.kite \
  compiler/backend/arm64/arm64.kite compiler/driver/klower.kite \
  || { echo "reseed FAILED"; exit 1; }
mv compiler/frontend/kfront bootstrap/kite-seed
chmod +x bootstrap/kite-seed
echo "reseeded bootstrap/kite-seed ($(wc -c <bootstrap/kite-seed) bytes)"
