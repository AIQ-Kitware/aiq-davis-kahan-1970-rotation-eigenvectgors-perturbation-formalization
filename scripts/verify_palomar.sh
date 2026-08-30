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
#   scripts/verify_palomar.sh yws-symmetric      # one entry, by directory name
#   scripts/verify_palomar.sh root               # the root comparator.json
#   scripts/verify_palomar.sh --static-only      # skip the exporter
#   scripts/verify_palomar.sh --fake-landrun     # no landrun available
#
# Three stages, cheapest first, each a real check rather than a proxy for one:
#
#   1. static preflight   scripts/check_palomar_readiness.py -- submodules, LFS,
#                         artifacts, licence, manifest pins, metadata shape,
#                         comparator keys, Challenge sizes and import closure
#   2. build              every `lean_lib` the lakefile declares, so the Challenge
#                         modules with their deliberate statement-side holes are
#                         built too, not only the default targets
#   3. comparator+NanoDa  the real exporter and the independent kernel; ground truth
#
# Stage 3 needs `comparator`, `lean4export` and `nanoda_bin`. Install them from
# https://github.com/leanprover/comparator and https://github.com/ammkrn/nanoda_lib,
# built at the Lean in `lean-toolchain` -- lean4export reads this repository's
# oleans directly, and an exporter built at another version fails with
# `incompatible header`, which looks like a broken statement rather than a version
# mismatch. `landrun` is the sandbox, not a check: without it, `--fake-landrun`
# runs the same commands unsandboxed and the comparison is unaffected.
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

# Entry discovery covers both submission layouts: Palomar's ordinary one, with a
# single `comparator.json` at the repository root, and the multi-entry one, with
# `registry/<entry>/comparator.json` selected explicitly at submission time.
config_for() {
    case "$1" in
        root) echo "comparator.json" ;;
        *)    echo "registry/$1/comparator.json" ;;
    esac
}

if [[ ${#ENTRIES[@]} -eq 0 ]]; then
    [[ -f comparator.json ]] && ENTRIES+=("root")
    if [[ -d registry ]]; then
        while IFS= read -r cfg; do
            ENTRIES+=("$(basename "$(dirname "$cfg")")")
        done < <(find registry -mindepth 2 -maxdepth 2 -name comparator.json | sort)
    fi
fi

if [[ ${#ENTRIES[@]} -eq 0 ]]; then
    echo "no comparator.json at the root and none under registry/*/" >&2
    exit 2
fi

# Every declared library, not just `defaultTargets`: a Challenge library is
# deliberately excluded from the default build because it carries holes, and it is
# exactly the thing that must compile before the exporter can read it.
LIBS=()
while IFS= read -r lib; do LIBS+=("$lib"); done < <(
    awk '/^\[\[lean_lib\]\]/{f=1;next} f && /^name[[:space:]]*=/{gsub(/[^"]*"/,"",$0);gsub(/".*/,"",$0);print;f=0}' lakefile.toml
)

echo "======================================================================"
echo "build: ${LIBS[*]:-<none declared>}"
echo "======================================================================"
BUILD_OK=1
for lib in ${LIBS[@]+"${LIBS[@]}"}; do
    lake build "$lib" || BUILD_OK=0
done

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
        elif ! command -v nanoda_bin >/dev/null 2>&1; then
            echo "    nanoda_bin is not on PATH. NanoDa is the second, independent"
            echo "    kernel and is a check, not a convenience; refusing to report a"
            echo "    pass without it. See the header of this script."
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
