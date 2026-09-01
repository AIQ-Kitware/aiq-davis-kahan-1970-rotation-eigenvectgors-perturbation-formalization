# ForTauCeti - reusable mathematics for Tau Ceti

`ForTauCeti` is the maintained reusable-mathematics product of this repository.
It is not a temporary holding directory to be drained into a submodule. Paper-
specific wrappers stay downstream; reusable definitions and proofs belong here
when they meet the package boundary.

Current repository policy is owned by [`../AGENTS.md`](../AGENTS.md). This README
keeps only the durable package contract. Mutable module counts, roadmap coverage,
readiness findings, and submission status belong to the manifest and checkers,
not to prose snapshots.

## Architecture

```text
Mathlib      TauCeti
   \          /
    ForTauCeti
        |
    DavisKahan and paper libraries
```

- `ForTauCeti` may depend on Mathlib, Tau Ceti, and itself.
- Paper libraries may consume `ForTauCeti`.
- `ForMathlib` is retired; historical documents may still mention its old paths
  and declaration names.
- Spectra is retired as a maintained dependency. Attribution remains in source
  headers, `retired/Spectra.UPSTREAM.md`, and the historical engineering records.
- Tau Ceti is a pinned Lake dependency, materialised under `.lake/packages`. An
  editable checkout is an optional explicit input (`--tauceti-root` /
  `TAUCETI_ROOT`). Coordination repositories under `submodules/` are not build
  dependencies. Maintained implementations are edited here.

The import firewall is enforced by `dev/policy/import-layers.yaml`.

## Namespace and API ownership

Declarations use their intended final `TauCeti.*` names from the start. The
module path is temporarily rooted at `ForTauCeti/`, but the declaration namespace
is not `ForTauCeti`.

When extending a Mathlib type namespace, keep the declaration under `TauCeti`,
for example:

```lean
namespace TauCeti
namespace ContinuousLinearMap

-- declarations

end ContinuousLinearMap
end TauCeti
```

Use `open TauCeti` where dot notation or unqualified lookup requires it. Avoid
creating new declarations in root Mathlib namespaces.

The maintained architecture has one canonical owner for each reusable concept.
When duplicate local APIs are found, compare their actual types and consumers,
choose the reusable owner here, migrate consumers in dependency order, and remove
the displaced definition or temporary adapter.

## Module style

New or substantially revised modules should use the Tau Ceti / Lean module style:

```lean
module

public import Mathlib...

/-!
# ...

## Provenance
...
-/

public section

namespace TauCeti
...
end TauCeti
```

Keep definition bodies hidden by default. Use per-declaration `@[expose]` only
when a consumer genuinely must unfold that definition, and document why. If a
consumer wants implementation details merely to make `rfl` or `change` work,
prefer a characteristic API lemma such as `foo_def`, `foo_apply`, or
`mem_foo_iff`.

Do not silence warnings or resource limits with local options merely to make a
module pass. The package is intended to be warning-clean under the Tau Ceti build
policy.

## Provenance

Every staged module should explain where its mathematics and Lean implementation
came from. Record the original repository/source, relevant source commit or paper,
original module/declaration names when useful, authorship/copyright and license,
extraction class (copied, adapted, generalized, specialized, or re-proved), and
any material semantic change.

Paper-specific theorem names and source transcriptions do not need to be moved
here merely because they are proved. Keep wrappers downstream when their purpose
is source fidelity rather than reusable API design.

## Manifest and readiness state

`dev/tauceti/extraction-manifest.json` is the source of truth for the current
module/cluster inventory. Generated and checkable artifacts own mutable status:

```bash
aiq-lean imports check dev/policy/import-layers.yaml
aiq-lean ratchet check dev/policy/ratchet.yaml
python3 scripts/check_tauceti_roadmap_topics.py
python3 scripts/check_tauceti_readiness.py
python3 scripts/derive_tauceti_submission_ladder.py --check
python3 scripts/export_for_tauceti.py --check
```

Do not copy the tools' current counts into this README. If a checker is no longer
load-bearing, follow `AGENTS.md`: prefer removing obsolete tooling to creating a
second status system around it.

## Tau Ceti export

Roadmaps and submission copies are derived from this maintained package. During
ordinary work, use `scripts/export_for_tauceti.py --check` to verify deterministic
mapping without modifying any checkout.

Only an explicit Tau Ceti submission task should run `--write`, which requires an
editable checkout, or advance the pinned Tau Ceti revision in `lake-manifest.json`. A submission copy is an output; deleting
`ForTauCeti` after export would delete the maintained product rather than finish
the work.

## What is historical

Long migration plans under `dev/tauceti/` can explain earlier ForMathlib, Spectra,
namespace, or submission decisions, but they are not current execution contracts.
Use the source tree, `AGENTS.md`, this package contract, and the maintained
manifest/checkers when an old record disagrees with the present repository.
