#!/bin/bash
REPO="$HOME/code/aiq-dkps-formalization/submodules/aiq-davis-kahan-1970-rotation-eigenvectgors-perturbation-formalization"
TOOLS="$HOME/.cache/palomar-tools-20260916"
BIN="$TOOLS/bin"

mkdir -p "$TOOLS" "$BIN"

SUBMISSION_TOOLCHAIN="$(tr -d '\r\n' < "$REPO/lean-toolchain")"

if [[ ! -d "$TOOLS/comparator/.git" ]]; then
    git clone --filter=blob:none \
        https://github.com/leanprover/comparator.git \
        "$TOOLS/comparator"
fi

git -C "$TOOLS/comparator" fetch origin \
    575674928e239f5bc452aab72d1dd7b0f1326494

git -C "$TOOLS/comparator" checkout --detach \
    575674928e239f5bc452aab72d1dd7b0f1326494

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

git -C "$TOOLS/lean4export" fetch origin \
    b18d673bd29b476466a51a3be1012df2ed322b10

git -C "$TOOLS/lean4export" checkout --detach \
    b18d673bd29b476466a51a3be1012df2ed322b10

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

git -C "$TOOLS/nanoda" fetch origin \
    68d5ca9db226849b41a6fff59d796ff19d0a8840

git -C "$TOOLS/nanoda" checkout --detach \
    68d5ca9db226849b41a6fff59d796ff19d0a8840

cargo build \
    --release \
    --locked \
    --manifest-path "$TOOLS/nanoda/Cargo.toml"

ln -sf \
    "$TOOLS/nanoda/target/release/nanoda_bin" \
    "$BIN/nanoda_bin"


GOBIN="$BIN" CGO_ENABLED=0 go install \
    github.com/zouuup/landrun/cmd/landrun@811cfff51ceaf3d9843708aa6d22e9b84ccac8b4


export PATH="$BIN:$PATH"

command -v comparator
command -v lean4export
command -v nanoda_bin
command -v landrun
