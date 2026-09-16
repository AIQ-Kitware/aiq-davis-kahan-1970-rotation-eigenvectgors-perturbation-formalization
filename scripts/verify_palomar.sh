#!/usr/bin/env bash
# Verify this Palomar Registry submission repository locally.
#
# This runs the checks we can run here. It is NOT Palomar's verification, it never
# contacts the registry, and passing it establishes nothing about acceptance.
# Registration is permanent and is a maintainer decision. An agent must not submit.
#
# It lives here rather than in the authoritative development repository because it
# asks whether *this* repository verifies. The development repository carried a
# copy until 2026-08-30; it is no longer a submission and no longer needs one.
#
# Usage:
#   scripts/verify_palomar.sh                    # ordinary root entry
#   scripts/verify_palomar.sh --static-only      # skip the exporter
#   scripts/verify_palomar.sh --fake-landrun     # no landrun available
#
# Three stages, cheapest first, each a real check rather than a proxy for one:
#
#   1. static preflight   scripts/check_palomar_readiness.py -- submodules, LFS,
#                         artifacts, licence, manifest pins, metadata shape,
#                         comparator keys, Challenge sizes and import closure
#   2. build              root Challenge and Solution modules selected by the
#                         conventional root comparator.json. Building the named
#                         modules is intentional: there is no aggregate
#                         `Palomar.lean`, because Challenge and Solution repeat
#                         the same declaration names in separate environments.
#   3. comparator+NanoDa  the real exporter and the independent kernel; ground truth
#
# Stage 3 needs `comparator`, `lean4export`, `nanoda_bin`, and (unless
# --fake-landrun is used) `landrun`. If they are not already on PATH, this
# script discovers the stable cache installed by build_verification_tools.sh and
# then the newest legacy dated cache. Build them against the Lean in
# `lean-toolchain`. Current Palomar verifier pins observed 2026-09-16 are:
#
#   comparator   575674928e239f5bc452aab72d1dd7b0f1326494
#   lean4export  b18d673bd29b476466a51a3be1012df2ed322b10
#   NanoDa       68d5ca9db226849b41a6fff59d796ff19d0a8840
#   landrun      811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
#
# Upstreams:
#   https://github.com/leanprover/comparator
#   https://github.com/leanprover/lean4export
#   https://github.com/robsimmons/nanoda_lib
#   https://github.com/zouuup/landrun
#
# `lean4export` reads this repository's oleans directly; an exporter built for a
# different Lean version fails with `incompatible header`, which can look like a
# broken statement. `landrun` is the sandbox, not a mathematical check:
# --fake-landrun runs the same Comparator/NanoDa commands unsandboxed.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Prefer an explicit caller PATH. If one or more verification tools are absent,
# augment it from the stable cache pointer maintained by
# scripts/build_verification_tools.sh. For backward compatibility with bundles
# created before that pointer existed, fall back to the newest dated bundle.
add_cached_palomar_tools_to_path() {
    local candidate
    local cache_parent="${PALOMAR_TOOLS_CACHE_PARENT:-$HOME/.cache}"
    local -a candidates=()
    local -a dated=()

    [[ -n "${PALOMAR_TOOLS_BIN:-}" ]] && candidates+=("$PALOMAR_TOOLS_BIN")
    candidates+=("$cache_parent/palomar-tools-latest/bin")

    shopt -s nullglob
    dated=("$cache_parent"/palomar-tools-[0-9]*/bin)
    shopt -u nullglob
    if [[ ${#dated[@]} -gt 0 ]]; then
        while IFS= read -r candidate; do
            candidates+=("$candidate")
        done < <(printf '%s\n' "${dated[@]}" | sort -r)
    fi

    for candidate in "${candidates[@]}"; do
        [[ -d "$candidate" ]] || continue
        if [[ -x "$candidate/comparator" && -x "$candidate/lean4export" \
            && -x "$candidate/nanoda_bin" && -x "$candidate/landrun" ]]; then
            PATH="$PATH:$candidate"
            export PATH
            echo "    added cached Palomar tools to PATH: $candidate"
            return 0
        fi
    done
    return 1
}

ENTRIES=()
STATIC_ONLY=0
FAKE_LANDRUN=0

while [[ $# -gt 0 ]]; do
    case "$1" in
        --all) ;;
        --static-only) STATIC_ONLY=1 ;;
        --fake-landrun) FAKE_LANDRUN=1 ;;
        -h|--help) sed -n '2,34p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
        -*) echo "unknown option: $1" >&2; exit 2 ;;
        *) ENTRIES+=("$1") ;;
    esac
    shift
done

# Palomar's ordinary layout has one root Comparator configuration.
config_for() {
    [[ "$1" == "root" ]] || return 1
    echo "comparator.json"
}

if [[ ${#ENTRIES[@]} -eq 0 ]]; then
    ENTRIES=("root")
elif [[ ${#ENTRIES[@]} -ne 1 || "${ENTRIES[0]}" != "root" ]]; then
    echo "ordinary single-entry layout accepts only the optional entry name 'root'" >&2
    exit 2
fi

[[ -f comparator.json ]] || { echo "no root comparator.json" >&2; exit 2; }

# Build the exact root modules Comparator will read. Do not build a synthetic
# `Palomar` root: Challenge and Solution deliberately repeat declaration names in
# separate environments.
BUILD_TARGETS=()
for entry in "${ENTRIES[@]}"; do
    cfg="$(config_for "$entry")"
    [[ -f "$cfg" ]] || continue
    while IFS= read -r module; do
        [[ -n "$module" ]] && BUILD_TARGETS+=("$module")
    done < <(python3 - "$cfg" <<'JSONPY'
import json
import pathlib
import sys

cfg = json.loads(pathlib.Path(sys.argv[1]).read_text())
for key in ("challenge_module", "solution_module"):
    module = cfg.get(key)
    if isinstance(module, str) and module:
        print(module)
JSONPY
    )
done

echo "======================================================================"
echo "build: ${BUILD_TARGETS[*]:-<none selected>}"
echo "======================================================================"
BUILD_OK=1
if [[ ${#BUILD_TARGETS[@]} -eq 0 ]]; then
    echo "no Challenge/Solution modules selected by comparator.json" >&2
    BUILD_OK=0
else
    lake build "${BUILD_TARGETS[@]}" || BUILD_OK=0
fi

FAILED=()
for entry in "${ENTRIES[@]}"; do
    cfg="$(config_for "$entry")"
    echo "======================================================================"
    echo "palomar entry: $entry  ($cfg)"
    echo "======================================================================"
    if [[ ! -f "$cfg" ]]; then
        echo "  no such entry: $cfg" >&2
        FAILED+=("$entry (missing config)")
        continue
    fi

    ok=$BUILD_OK
    [[ $BUILD_OK -eq 1 ]] || echo "--- build FAILED above; later stages are not meaningful"

    echo "--- 1/3 static preflight"
    python3 scripts/check_palomar_readiness.py --entry root || ok=0

    echo "--- 2/3 build: done above"

    if [[ $STATIC_ONLY -eq 1 ]]; then
        echo "--- 3/3 comparator: skipped (--static-only)"
        echo "    Not a pass. The exporter is ground truth and did not run."
    else
        echo "--- 3/3 comparator + NanoDa"
        if ! command -v comparator >/dev/null 2>&1 \
            || ! command -v lean4export >/dev/null 2>&1 \
            || ! command -v nanoda_bin >/dev/null 2>&1 \
            || { [[ $FAKE_LANDRUN -eq 0 && -z "${COMPARATOR_LANDRUN:-}" ]] \
                && ! command -v landrun >/dev/null 2>&1; }; then
            add_cached_palomar_tools_to_path || true
        fi
        if ! command -v comparator >/dev/null 2>&1; then
            echo "    comparator was not found on PATH or in a cached Palomar tool bundle."
            echo "    Run scripts/build_verification_tools.sh."
            ok=0
        elif ! command -v lean4export >/dev/null 2>&1; then
            echo "    lean4export was not found on PATH or in a cached Palomar tool bundle."
            echo "    Run scripts/build_verification_tools.sh."
            ok=0
        elif ! command -v nanoda_bin >/dev/null 2>&1; then
            echo "    nanoda_bin was not found on PATH or in a cached Palomar tool bundle."
            echo "    NanoDa is the second, independent kernel and is a check, not a"
            echo "    convenience; refusing to report a pass without it."
            echo "    Run scripts/build_verification_tools.sh."
            ok=0
        elif [[ $FAKE_LANDRUN -eq 0 && -z "${COMPARATOR_LANDRUN:-}" ]] \
            && ! command -v landrun >/dev/null 2>&1; then
            echo "    landrun was not found on PATH or in a cached Palomar tool bundle."
            echo "    Run scripts/build_verification_tools.sh or pass --fake-landrun."
            ok=0
        else
            if [[ $FAKE_LANDRUN -eq 1 && -z "${COMPARATOR_LANDRUN:-}" ]]; then
                echo "    landrun is bypassed (--fake-landrun): the exporter runs"
                echo "    unsandboxed. That is a weaker sandbox, not a weaker check."
                # Comparator invokes landrun with its own flags, so the bypass has
                # to be a shim that discards them rather than a bare `env`.
                SHIM="$(mktemp)"
                cat > "$SHIM" <<'SHIM_EOF'
#!/usr/bin/env bash
set -euo pipefail
value_flags=(--ro --rox --rw --rwx --bind-tcp --connect-tcp --log-level --env)
while [[ $# -gt 0 ]]; do
  case "$1" in
    --) shift; break ;;
    -*) for vf in "${value_flags[@]}"; do [[ "$1" == "$vf" ]] && shift && break; done; shift ;;
    *) break ;;
  esac
done
[[ $# -gt 0 ]] || { echo "landrun shim: no command given" >&2; exit 2; }
echo "NOT LANDRUN: running unsandboxed: $*" >&2
exec "$@"
SHIM_EOF
                chmod +x "$SHIM"
                export COMPARATOR_LANDRUN="$SHIM"
                trap 'rm -f "$SHIM"' EXIT
            fi
            # `lake env` is required: the exporter needs the Lake search path to
            # find this repository's compiled modules.
            lake env comparator "$cfg" || ok=0
        fi
    fi

    [[ $ok -eq 1 ]] || FAILED+=("$entry")
    echo
done

echo "======================================================================"
if [[ ${#FAILED[@]} -eq 0 ]]; then
    echo "palomar verify: OK for ${#ENTRIES[@]} entry/entries"
    echo
    echo "  Locally verified only. This is not Palomar verification, not"
    echo "  acceptance, and not registration. The maintainer reviews the prepared"
    echo "  commit and submits; an agent must not."
    exit 0
fi
echo "palomar verify: FAILED for ${#FAILED[@]} of ${#ENTRIES[@]}: ${FAILED[*]}"
exit 1
