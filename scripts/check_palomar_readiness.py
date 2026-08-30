#!/usr/bin/env python3
"""Static preflight for this Palomar Registry submission repository.

This is **not** Palomar's verification, and passing it establishes nothing about
acceptance. It checks the mechanical requirements that can be checked here, so a
defect is found before a submission is prepared rather than after. Registration is
permanent, which is why it is worth having a tripwire at all.

It lives here, not in the authoritative development repository, because it asks
whether *this* repository is submittable. That question belongs to the repository
being submitted. The development repository carried a copy until 2026-08-30, where
it answered the wrong question -- it reported the coordination submodules there as
a fatal defect, which they are not, because that repository is not submitted.

What it checks:

  repository   no submodules, no LFS pointers, no committed build artifacts, one
               conventional root licence, size under the policy cap
  lake         one root lakefile, a committed manifest, every dependency a
               credential-free HTTPS URL pinned to a full 40-character lowercase
               SHA, no path dependencies, toolchain at or above the minimum
  metadata     formalization.yaml is v0.4, has the required fields, its licence
               matches the root LICENSE, declares no thin-wrapper target, and
               carries no leftover template text
  comparator   only accepted keys, a nonempty theorem list, exactly the three
               permitted axioms, and modules whose sources exist
  challenge    within the size caps, and -- the one that matters -- no module in
               its transitive import closure resolves to a source file in this
               repository except the Challenge itself

The import-closure check is the reason this script exists. A Challenge may reach
only Lean core and the allowlisted Mathlib/Tau Ceti/CSLib closure; one stray
`import ForTauCeti.…` five modules deep is invisible to a reader and fatal to a
submission.

Both submission layouts are handled. Palomar's ordinary layout puts one
`comparator.json` at the repository root; a repository carrying several entries
puts one per directory under `registry/`, each with its own `formalization.yaml`
beside it, and selects both paths explicitly at submission time. Entries are
discovered in whichever shape is present.

**This script does not check Palomar's metadata schema itself.** Palomar's own
verifier is the authority for that, it moves, and a hand-written second copy of
its rules would drift. What is checked here are the local, structural facts. Run
Palomar's `scripts/submission_contract.py` from the `PalomarSubmission`
repository against each `formalization.yaml` for the schema.

Axiom closure needs Lean and is behind `--with-axioms`, which shells out to
`lake env lean`. `scripts/verify_palomar.sh` runs the real Comparator.

Usage:
    python3 scripts/check_palomar_readiness.py
    python3 scripts/check_palomar_readiness.py --entry yws-symmetric
    python3 scripts/check_palomar_readiness.py --with-axioms
"""
from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
#: A multi-entry repository keeps one directory per entry here. A repository
#: using Palomar's ordinary layout has no such directory and one root config.
ENTRY_DIR = ROOT / "registry"

#: From PalomarSubmission/toolchains.json, read 2026-08-28. Override with
#: --min-toolchain when Palomar raises it; this is a snapshot, not an authority.
MIN_TOOLCHAIN = (4, 28, 0)

PERMITTED_AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
COMPARATOR_KEYS = {
    "challenge_module", "solution_module", "theorem_names",
    "definition_names", "permitted_axioms", "enable_nanoda",
}
REQUIRED_COMPARATOR_KEYS = {"challenge_module", "solution_module", "theorem_names"}

ARTIFACT_SUFFIXES = {
    ".olean", ".ilean", ".a", ".bc", ".dll", ".dylib", ".o", ".obj", ".so", ".trace",
}
SIZE_CAP_BYTES = 500 * 1024 * 1024
CHALLENGE_HARD_LINES, CHALLENGE_HARD_BYTES = 1000, 100 * 1024
CHALLENGE_WARN_LINES, CHALLENGE_WARN_BYTES = 300, 32 * 1024

IMPORT_RE = re.compile(r"^\s*(?:public\s+|private\s+|meta\s+)*import\s+([A-Za-z0-9_.]+)", re.M)
#: The literal sentinels the official template and our wrapper skeleton use.
#: Case-sensitive on purpose: a case-insensitive match fires on ordinary prose
#: such as "prompt template:", which is not a placeholder.
TEMPLATE_RE = re.compile(r"TEMPLATE:|REPLACE_WITH_")


class Report:
    def __init__(self) -> None:
        self.problems: list[str] = []
        self.warnings: list[str] = []
        self.notes: list[str] = []

    def fail(self, msg: str) -> None:
        self.problems.append(msg)

    def warn(self, msg: str) -> None:
        self.warnings.append(msg)

    def note(self, msg: str) -> None:
        self.notes.append(msg)


def git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True,
                          text=True).stdout


# ---------------------------------------------------------------- repository

def check_repository(rep: Report) -> None:
    if (ROOT / ".gitmodules").exists():
        rep.fail(".gitmodules exists; Palomar rejects a repository with submodules")
    gitlinks = [ln.split("\t")[-1] for ln in git("ls-files", "-s").splitlines()
                if ln.startswith("160000")]
    for path in gitlinks:
        rep.fail(f"submodule gitlink still tracked: {path}")

    tracked = [ln for ln in git("ls-files").splitlines() if ln]
    artifacts = [f for f in tracked if pathlib.Path(f).suffix in ARTIFACT_SUFFIXES]
    for f in artifacts[:10]:
        rep.fail(f"compiled artifact is tracked: {f}")

    total = 0
    lfs = []
    for f in tracked:
        p = ROOT / f
        if not p.is_file() or p.is_symlink():
            continue
        total += p.stat().st_size
        if p.stat().st_size < 200:
            try:
                head = p.read_bytes()[:60]
            except OSError:
                continue
            if head.startswith(b"version https://git-lfs"):
                lfs.append(f)
    for f in lfs:
        rep.fail(f"Git LFS pointer is tracked: {f}")
    if total > SIZE_CAP_BYTES:
        rep.fail(f"tracked content {total / 2**20:.0f} MiB exceeds the 500 MiB cap")
    else:
        rep.note(f"tracked content {total / 2**20:.1f} MiB (cap 500 MiB)")

    licences = [f for f in tracked
                if pathlib.PurePosixPath(f).name.upper() in {"LICENSE", "LICENCE", "COPYING"}]
    if len(licences) != 1:
        rep.fail(f"expected exactly one conventional root licence file, found {licences}")
    elif "/" in licences[0]:
        rep.fail(f"licence file is not at the repository root: {licences[0]}")


# ---------------------------------------------------------------------- lake

def check_lake(rep: Report, min_toolchain: tuple[int, int, int]) -> None:
    toml, lean = ROOT / "lakefile.toml", ROOT / "lakefile.lean"
    if toml.exists() and lean.exists():
        rep.fail("both lakefile.toml and lakefile.lean exist; Palomar wants exactly one")
    elif not toml.exists() and not lean.exists():
        rep.fail("no root lakefile")

    tc = ROOT / "lean-toolchain"
    if not tc.exists():
        rep.fail("no lean-toolchain")
    else:
        raw = tc.read_text().strip()
        m = re.search(r"v(\d+)\.(\d+)\.(\d+)", raw)
        if not m:
            rep.warn(f"cannot parse lean-toolchain {raw!r}")
        else:
            got = tuple(int(x) for x in m.groups())
            if got < min_toolchain:
                rep.fail(f"lean-toolchain {raw} is below the minimum "
                         f"v{'.'.join(map(str, min_toolchain))}")
            else:
                rep.note(f"lean-toolchain {raw} (minimum "
                         f"v{'.'.join(map(str, min_toolchain))})")

    man = ROOT / "lake-manifest.json"
    if not man.exists():
        rep.fail("lake-manifest.json is not committed")
        return
    if "lake-manifest.json" not in git("ls-files", "lake-manifest.json"):
        rep.fail("lake-manifest.json exists but is not tracked")
    data = json.loads(man.read_text())
    for pkg in data.get("packages", []):
        name = pkg.get("name", "?")
        if pkg.get("type") != "git":
            rep.fail(f"dependency {name} is not a git dependency "
                     f"(type {pkg.get('type')!r}); a path dependency cannot be "
                     f"fetched by a consumer")
            continue
        url = pkg.get("url", "")
        if not url.startswith("https://github.com/"):
            rep.fail(f"dependency {name} url is not a credential-free "
                     f"https://github.com/ URL: {url}")
        if "@" in url:
            rep.fail(f"dependency {name} url appears to carry credentials: {url}")
        rev = pkg.get("rev", "")
        if not re.fullmatch(r"[0-9a-f]{40}", rev):
            rep.fail(f"dependency {name} revision is not a full 40-character "
                     f"lowercase SHA: {rev!r}")
    rep.note(f"{len(data.get('packages', []))} dependencies, all git-pinned")


# ------------------------------------------------------------------ metadata

def check_metadata(rep: Report, path: pathlib.Path) -> None:
    try:
        import yaml
    except ImportError:
        rep.warn(f"PyYAML unavailable; skipped metadata checks for {rel(path)}")
        return
    doc = yaml.safe_load(path.read_text())
    where = rel(path)
    if doc.get("version") != "v0.4":
        rep.fail(f"{where}: version is {doc.get('version')!r}, expected v0.4")

    proj = doc.get("project") or {}
    for field in ("name", "description", "authors", "license", "responsible_maintainers"):
        if not proj.get(field):
            rep.fail(f"{where}: project.{field} is missing or empty")

    lic_file = ROOT / "LICENSE"
    if lic_file.exists() and proj.get("license") == "Apache-2.0":
        if "Apache License" not in lic_file.read_text()[:4000]:
            rep.fail(f"{where}: project.license is Apache-2.0 but LICENSE does not "
                     f"look like the Apache licence")

    if not (doc.get("sources") or []):
        rep.fail(f"{where}: sources is empty; at least one is required")
    valid_rel = {"formalizes", "adapts", "independently-proves", "background", "other", ""}
    origin_ok = False
    for i, src in enumerate(doc.get("sources") or []):
        if not src.get("title"):
            rep.fail(f"{where}: sources[{i}] has no title")
        r = src.get("relationship")
        if r is not None and r not in valid_rel:
            rep.fail(f"{where}: sources[{i}].relationship {r!r} is not a schema value")
        if r in {"formalizes", "adapts", "independently-proves"}:
            origin_ok = True
        if src.get("type") == "original-proof":
            origin_ok = True
    if not origin_ok:
        rep.fail(f"{where}: no source declares formalizes/adapts/independently-proves "
                 f"and none is an original-proof; exactly one result origin is required")

    if not ((doc.get("automation") or {}).get("methods")):
        rep.fail(f"{where}: automation.methods is missing or empty")
    if not ((doc.get("review") or {}).get("status")):
        rep.fail(f"{where}: review.status is missing or empty")

    cls = doc.get("classification") or {}
    if not cls.get("arxiv"):
        rep.warn(f"{where}: classification.arxiv is empty")
    for code in cls.get("msc2020") or []:
        if not re.fullmatch(r"[0-9]{2}[0-9A-Za-z]{3}", str(code)):
            rep.fail(f"{where}: msc2020 code {code!r} is not five characters")

    repo = doc.get("repository") or {}
    if repo.get("substantive_formalization"):
        rep.fail(f"{where}: declares repository.substantive_formalization, which "
                 f"marks the repository a thin wrapper; this one carries the proof "
                 f"and is the substantive development")
    if repo.get("role") == "thin-wrapper":
        rep.fail(f"{where}: declares repository.role: thin-wrapper; this repository "
                 f"carries the proof")
    if repo:
        rep.warn(f"{where}: has a `repository` block; current policy omits it "
                 f"entirely for a substantive development")

    hits = TEMPLATE_RE.findall(path.read_text())
    if hits:
        rep.fail(f"{where}: leftover template/placeholder text ({len(hits)} occurrence(s))")


# ---------------------------------------------------------- module resolution

def local_lib_roots() -> list[pathlib.Path]:
    """Directories under which a module name may resolve to a source file here."""
    roots = [ROOT]
    text = (ROOT / "lakefile.toml").read_text() if (ROOT / "lakefile.toml").exists() else ""
    for m in re.finditer(r'srcDir\s*=\s*"([^"]+)"', text):
        roots.append(ROOT / m.group(1))
    return roots


def local_source_for(module: str) -> pathlib.Path | None:
    rel_path = pathlib.Path(module.replace(".", "/") + ".lean")
    for root in local_lib_roots():
        candidate = root / rel_path
        if candidate.is_file():
            return candidate
    return None


def challenge_closure(rep: Report, entry: str, module: str) -> None:
    """Every module a Challenge transitively imports must come from outside here."""
    start = local_source_for(module)
    if start is None:
        rep.fail(f"{entry}: challenge module {module} has no source file")
        return

    size = start.stat().st_size
    lines = start.read_text().count("\n") + 1
    if lines > CHALLENGE_HARD_LINES or size > CHALLENGE_HARD_BYTES:
        rep.fail(f"{entry}: challenge is {lines} lines / {size} bytes, over the hard "
                 f"cap of {CHALLENGE_HARD_LINES} lines / {CHALLENGE_HARD_BYTES} bytes")
    elif lines > CHALLENGE_WARN_LINES or size > CHALLENGE_WARN_BYTES:
        rep.warn(f"{entry}: challenge is {lines} lines / {size} bytes, over the "
                 f"preferred {CHALLENGE_WARN_LINES} lines / {CHALLENGE_WARN_BYTES} bytes")
    else:
        rep.note(f"{entry}: challenge {lines} lines / {size} bytes")

    seen, stack, leaked = {module}, [(module, start)], []
    while stack:
        mod, path = stack.pop()
        for imported in IMPORT_RE.findall(path.read_text()):
            if imported in seen:
                continue
            seen.add(imported)
            src = local_source_for(imported)
            if src is None:
                continue  # external: Lean core, Mathlib, Tau Ceti closure
            leaked.append((imported, mod))
            stack.append((imported, src))
    for imported, via in sorted(set(leaked)):
        rep.fail(f"{entry}: challenge closure reaches local module {imported} "
                 f"(via {via}); a Palomar Challenge may import only Lean core and "
                 f"the allowlisted Mathlib/Tau Ceti closure")
    if not leaked:
        rep.note(f"{entry}: challenge closure is clean "
                 f"({len(seen) - 1} direct/transitive imports, none local)")


# ---------------------------------------------------------------- comparator

def entry_name(cfg_path: pathlib.Path) -> str:
    """The entry's label: its directory under `registry/`, or `root`."""
    return "root" if cfg_path.parent == ROOT else cfg_path.parent.name


def check_entry(rep: Report, cfg_path: pathlib.Path, *, with_axioms: bool) -> None:
    entry = entry_name(cfg_path)
    try:
        cfg = json.loads(cfg_path.read_text())
    except json.JSONDecodeError as exc:
        rep.fail(f"{entry}: comparator.json is not valid JSON: {exc}")
        return

    unknown = set(cfg) - COMPARATOR_KEYS
    if unknown:
        rep.fail(f"{entry}: comparator.json has non-accepted key(s) {sorted(unknown)}")
    missing = REQUIRED_COMPARATOR_KEYS - set(cfg)
    if missing:
        rep.fail(f"{entry}: comparator.json is missing {sorted(missing)}")
        return
    if not cfg["theorem_names"]:
        rep.fail(f"{entry}: theorem_names is empty")
    if sorted(cfg.get("permitted_axioms", [])) != sorted(PERMITTED_AXIOMS):
        rep.fail(f"{entry}: permitted_axioms must be exactly {PERMITTED_AXIOMS}, "
                 f"got {cfg.get('permitted_axioms')}")
    if cfg.get("enable_nanoda") is not True:
        rep.warn(f"{entry}: enable_nanoda is not true; the official template sets it")

    for key in ("challenge_module", "solution_module"):
        if local_source_for(cfg[key]) is None:
            rep.fail(f"{entry}: {key} {cfg[key]} has no source file")
    if cfg["challenge_module"] == cfg["solution_module"]:
        rep.fail(f"{entry}: challenge and solution must be distinct modules")

    if local_source_for(cfg["challenge_module"]) is not None:
        challenge_closure(rep, entry, cfg["challenge_module"])

    # An entry carries its metadata one of three ways. Preferred: a per-entry
    # `formalization.yaml` beside the config, which a submission selects
    # explicitly alongside the Comparator path -- that is how two entries over the
    # same paper record different source relationships. Otherwise the extracted
    # entry repository's ROOT file describes it (readiness §5.0), or, in the
    # superseded thin-wrapper design, a skeleton under `wrapper/`. Absence of a
    # skeleton is not a finding -- warning about it trained readers to ignore this
    # checker's output.
    entry_meta = cfg_path.parent / "formalization.yaml"
    if entry_meta.exists() and entry_meta != ROOT / "formalization.yaml":
        check_metadata(rep, entry_meta)
        rep.note(f"{entry}: metadata at {rel(entry_meta)}, selected with this config")
    else:
        rep.note(f"{entry}: uses the root formalization.yaml")

    if with_axioms:
        check_axioms(rep, entry, cfg)


def check_axioms(rep: Report, entry: str, cfg: dict) -> None:
    names = list(cfg["theorem_names"]) + list(cfg.get("definition_names") or [])
    probe = ROOT / ".lake" / f"palomar-axioms-{entry}.lean"
    probe.parent.mkdir(parents=True, exist_ok=True)
    probe.write_text(f"import {cfg['solution_module']}\n"
                     + "".join(f"#print axioms {n}\n" for n in names))
    try:
        done = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT,
                              capture_output=True, text=True, timeout=1800)
    except subprocess.TimeoutExpired:
        rep.fail(f"{entry}: axiom probe timed out")
        return
    finally:
        probe.unlink(missing_ok=True)
    out = done.stdout + done.stderr
    if done.returncode != 0:
        rep.fail(f"{entry}: axiom probe failed:\n{out.strip()[:600]}")
        return
    for name in names:
        line = next((ln for ln in out.splitlines() if ln.startswith(f"'{name}'")), None)
        if line is None:
            rep.fail(f"{entry}: {name} did not resolve in {cfg['solution_module']}")
            continue
        if "does not depend on any axioms" in line:
            rep.note(f"{entry}: {name} depends on no axioms")
            continue
        found = re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", line.split("axioms:")[-1])
        bad = [a for a in found if a not in PERMITTED_AXIOMS]
        if bad:
            rep.fail(f"{entry}: {name} depends on forbidden axiom(s) {bad}")
        else:
            rep.note(f"{entry}: {name} axiom closure is clean")


def rel(p: pathlib.Path) -> str:
    try:
        return str(p.relative_to(ROOT))
    except ValueError:
        return str(p)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--entry", default=None, help="check only this registry/<entry>")
    ap.add_argument("--with-axioms", action="store_true",
                    help="also run `lake env lean` to audit each solution's axiom closure")
    ap.add_argument("--min-toolchain", default=None,
                    help="override the recorded minimum, e.g. v4.28.0")
    args = ap.parse_args(argv)

    minimum = MIN_TOOLCHAIN
    if args.min_toolchain:
        m = re.search(r"v?(\d+)\.(\d+)\.(\d+)", args.min_toolchain)
        if not m:
            print(f"cannot parse --min-toolchain {args.min_toolchain!r}", file=sys.stderr)
            return 2
        minimum = tuple(int(x) for x in m.groups())

    rep = Report()
    check_repository(rep)
    check_lake(rep, minimum)
    root_meta = ROOT / "formalization.yaml"
    if root_meta.exists():
        check_metadata(rep, root_meta)
    else:
        rep.fail("no root formalization.yaml")

    configs = sorted(ENTRY_DIR.glob("*/comparator.json"))
    root_cfg = ROOT / "comparator.json"
    if root_cfg.exists():
        configs.insert(0, root_cfg)
    if args.entry:
        configs = [c for c in configs if entry_name(c) == args.entry]
        if not configs:
            print(f"no such entry: {args.entry}", file=sys.stderr)
            return 2
    if not configs:
        rep.warn("no comparator.json at the root and none under registry/*/")
    for cfg in configs:
        check_entry(rep, cfg, with_axioms=args.with_axioms)

    for note in rep.notes:
        print(f"  ok    {note}")
    for warning in rep.warnings:
        print(f"  warn  {warning}")
    for problem in rep.problems:
        print(f"  FAIL  {problem}")
    print()
    if rep.problems:
        print(f"palomar readiness: {len(rep.problems)} problem(s), "
              f"{len(rep.warnings)} warning(s)")
        return 1
    print(f"palomar readiness: OK ({len(configs)} entry/entries, "
          f"{len(rep.warnings)} warning(s))")
    print("  This is a local preflight, not Palomar verification or acceptance.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
