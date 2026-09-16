#!/usr/bin/env bash
# Build the exact Palomar verification tools used by this repository's local
# verifier. The dated bundle records the pin set; `palomar-tools-latest` is a
# stable local pointer to the most recently completed pinned bundle.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CACHE_PARENT="${PALOMAR_TOOLS_CACHE_PARENT:-$HOME/.cache}"
BUNDLE_TAG="${PALOMAR_TOOLS_BUNDLE_TAG:-20260916}"
TOOLS="$CACHE_PARENT/palomar-tools-$BUNDLE_TAG"
LATEST="$CACHE_PARENT/palomar-tools-latest"
BIN="$TOOLS/bin"

COMPARATOR_REV="575674928e239f5bc452aab72d1dd7b0f1326494"
LEAN4EXPORT_REV="b18d673bd29b476466a51a3be1012df2ed322b10"
NANODA_REV="68d5ca9db226849b41a6fff59d796ff19d0a8840"
LANDRUN_REV="811cfff51ceaf3d9843708aa6d22e9b84ccac8b4"

mkdir -p "$TOOLS" "$BIN"

SUBMISSION_TOOLCHAIN="$(tr -d '\r\n' < "$ROOT/lean-toolchain")"

if [[ ! -d "$TOOLS/comparator/.git" ]]; then
    git clone --filter=blob:none \
        https://github.com/leanprover/comparator.git \
        "$TOOLS/comparator"
fi

git -C "$TOOLS/comparator" fetch origin "$COMPARATOR_REV"
git -C "$TOOLS/comparator" checkout --detach "$COMPARATOR_REV"
(
    cd "$TOOLS/comparator"
    ELAN_TOOLCHAIN="$SUBMISSION_TOOLCHAIN" lake build comparator
)
ln -sf \
    "$TOOLS/comparator/.lake/build/bin/comparator" \
    "$BIN/comparator"

if [[ ! -d "$TOOLS/lean4export/.git" ]]; then
    git clone --filter=blob:none \
        https://github.com/leanprover/lean4export.git \
        "$TOOLS/lean4export"
fi

git -C "$TOOLS/lean4export" fetch origin "$LEAN4EXPORT_REV"
git -C "$TOOLS/lean4export" checkout --detach "$LEAN4EXPORT_REV"
(
    cd "$TOOLS/lean4export"
    ELAN_TOOLCHAIN="$SUBMISSION_TOOLCHAIN" lake build lean4export
)
ln -sf \
    "$TOOLS/lean4export/.lake/build/bin/lean4export" \
    "$BIN/lean4export"

if [[ ! -d "$TOOLS/nanoda/.git" ]]; then
    git clone --filter=blob:none \
        https://github.com/robsimmons/nanoda_lib.git \
        "$TOOLS/nanoda"
fi

git -C "$TOOLS/nanoda" fetch origin "$NANODA_REV"
git -C "$TOOLS/nanoda" checkout --detach "$NANODA_REV"
cargo build \
    --release \
    --locked \
    --manifest-path "$TOOLS/nanoda/Cargo.toml"
ln -sf \
    "$TOOLS/nanoda/target/release/nanoda_bin" \
    "$BIN/nanoda_bin"

GOBIN="$BIN" CGO_ENABLED=0 go install \
    "github.com/zouuup/landrun/cmd/landrun@$LANDRUN_REV"

for tool in comparator lean4export nanoda_bin landrun; do
    if [[ ! -x "$BIN/$tool" ]]; then
        echo "verification tool build did not produce an executable: $BIN/$tool" >&2
        exit 1
    fi
done

# Publish the stable pointer only after the whole pinned bundle succeeded. This
# deliberately means "latest bundle installed by this script", not "un-pinned
# latest upstream release"; reproducibility against Palomar's verifier matters.
if [[ -e "$LATEST" && ! -L "$LATEST" ]]; then
    echo "refusing to replace non-symlink stable tool path: $LATEST" >&2
    exit 1
fi
ln -sfn "$TOOLS" "$LATEST"

cat <<EOF2
Palomar verification tools are ready.

Pinned bundle:  $TOOLS
Stable pointer: $LATEST
Verifier bin:   $LATEST/bin

scripts/verify_palomar.sh discovers the stable pointer automatically, so no
persistent PATH edit is required. For direct interactive use of the tools:

  export PATH="$LATEST/bin:\$PATH"
EOF2
