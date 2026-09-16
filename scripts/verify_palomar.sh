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
#   scripts/verify_palomar.sh                    # every entry
#   scripts/verify_palomar.sh dk-section-two    # the selected entry
#   scripts/verify_palomar.sh --static-only      # skip the exporter
#   scripts/verify_palomar.sh --fake-landrun     # no landrun available
#
# Three stages, cheapest first, each a real check rather than a proxy for one:
#
#   1. static preflight   scripts/check_palomar_readiness.py -- submodules, LFS,
#                         artifacts, licence, manifest pins, metadata shape,
#                         comparator keys, Challenge sizes and import closure
#   2. build              every Challenge and Solution module selected by a
#                         registry Comparator configuration. Building the named
#                         modules is intentional: there is no aggregate
#                         `Palomar.lean`, because Challenge and Solution repeat
#                         the same declaration names in separate environments.
#   3. comparator+NanoDa  the real exporter and the independent kernel; ground truth
#
# Stage 3 needs `comparator`, `lean4export`, `nanoda_bin`, and (unless
# --fake-landrun is used) `landrun`. Build them against the Lean in
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

# Entry discovery remains generic, but this repository intentionally uses only
# `registry/dk-section-two/comparator.json`; there is no stale root entry.
config_for() {
    echo "registry/$1/comparator.json"
}

if [[ ${#ENTRIES[@]} -eq 0 ]]; then
    if [[ -d registry ]]; then
        while IFS= read -r cfg; do
            ENTRIES+=("$(basename "$(dirname "$cfg")")")
        done < <(find registry -mindepth 2 -maxdepth 2 -name comparator.json | sort)
    fi
fi

if [[ ${#ENTRIES[@]} -eq 0 ]]; then
    echo "no comparator.json under registry/*/" >&2
    exit 2
fi

# Build the exact modules Comparator will read. Do not build a synthetic
# `Palomar` root: this repository intentionally has no `Palomar.lean`, and the
# readiness checker rejects one as a stale aggregate submission surface.
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
    echo "no Challenge/Solution modules selected by registry configs" >&2
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
    python3 scripts/check_palomar_readiness.py --entry "$entry" || ok=0

    echo "--- 2/3 build: done above"

    if [[ $STATIC_ONLY -eq 1 ]]; then
        echo "--- 3/3 comparator: skipped (--static-only)"
        echo "    Not a pass. The exporter is ground truth and did not run."
    else
        echo "--- 3/3 comparator + NanoDa"
        if ! command -v comparator >/dev/null 2>&1; then
            echo "    comparator is not on PATH; see the header of this script."
            ok=0
        elif ! command -v lean4export >/dev/null 2>&1; then
            echo "    lean4export is not on PATH; see the header of this script."
            ok=0
        elif ! command -v nanoda_bin >/dev/null 2>&1; then
            echo "    nanoda_bin is not on PATH. NanoDa is the second, independent"
            echo "    kernel and is a check, not a convenience; refusing to report a"
            echo "    pass without it. See the header of this script."
            ok=0
        elif [[ $FAKE_LANDRUN -eq 0 && -z "${COMPARATOR_LANDRUN:-}" ]] \
            && ! command -v landrun >/dev/null 2>&1; then
            echo "    landrun is not on PATH. Install it or pass --fake-landrun."
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
