"""End-to-end deterministic verification and SHA-256 manifest audit for OUH-CERT-1.0.

Author: Lluis Eriksson
License: MIT
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from typing import Dict, List

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
if str(ROOT / "tests") not in sys.path:
    sys.path.insert(0, str(ROOT / "tests"))

from src.ouh_certifier import verify_certificate
from test_suite import run_red_team_suite

TRACKED_DIRS = ["lean", "src", "scripts", "tests", "certificates", "data", "figures"]
TRACKED_FILES = ["LICENSE", "README.md", "pyproject.toml", "paper/main.tex", "paper/references.bib"]
EXCLUDED_NAMES = {"SHA256_MANIFEST.json", "lake-manifest.json"}
EXCLUDED_EXTS = {".pyc", ".olean", ".ilean", ".c", ".pdf"}

EXPECTED_THEOREMS = [
    "ObliviousUnambiguous.lex_lt_irrefl_and_asymm",
    "ObliviousUnambiguous.canonical_advice_unique",
    "ObliviousUnambiguous.prefix_search_bit_recovery",
    "ObliviousUnambiguous.co_onp_tester_singleton",
    "ObliviousUnambiguous.mahaney_census_exact_subset",
    "ObliviousUnambiguous.cantor_pairing_injective",
    "ObliviousUnambiguous.oblivious_witness_bit_extraction",
    "ObliviousUnambiguous.oblivious_empty_slice_default_zero",
    "ObliviousUnambiguous.loose_tower_round_bound",
    "ObliviousUnambiguous.loose_tower_disagreement_descent",
    "ObliviousUnambiguous.loose_generator_set_growth_monotone",
    "ObliviousUnambiguous.dot_op_co_oup_probe_refutation",
    "ObliviousUnambiguous.dot_op_collapse_unique_pair",
    "ObliviousUnambiguous.dot_op_hierarchy_idempotence",
    "ObliviousUnambiguous.single_loose_query_guarded",
    "ObliviousUnambiguous.input_tagging_preserves_obliviousness",
    "ObliviousUnambiguous.soup_unique_bit_witness",
    "ObliviousUnambiguous.class_containment_chain_complete",
]


def _sha256(path: Path) -> str:
    h = hashlib.sha256()
    h.update(path.read_bytes())
    return h.hexdigest()


def collect_tracked_files() -> List[Path]:
    found: List[Path] = []
    for rel in TRACKED_FILES:
        p = ROOT / rel
        if p.exists():
            found.append(p)
    for dname in TRACKED_DIRS:
        d = ROOT / dname
        if not d.exists():
            continue
        for p in sorted(d.rglob("*")):
            if not p.is_file():
                continue
            if any(part in {"__pycache__", ".lake", ".git"} for part in p.parts):
                continue
            if p.name in EXCLUDED_NAMES or p.suffix in EXCLUDED_EXTS:
                continue
            found.append(p)
    return sorted(set(found), key=lambda x: x.relative_to(ROOT).as_posix())


def audit_zero_float_sources() -> None:
    forbidden = ("float(", "math.", "numpy")
    for p in sorted((ROOT / "src").glob("*.py")):
        txt = p.read_text(encoding="utf-8")
        for tok in forbidden:
            if tok in txt:
                raise RuntimeError(f"Forbidden token {tok!r} found in {p.relative_to(ROOT)}")


def audit_lean_kernel() -> None:
    lean_dir = ROOT / "lean"
    src_txt = (lean_dir / "ObliviousUnambiguous.lean").read_text(encoding="utf-8")
    if "sorry" in src_txt or "axiom " in src_txt:
        raise RuntimeError("Lean source contains sorry or axiom declaration")

    res_build = subprocess.run(["lake", "build"], cwd=lean_dir, capture_output=True, text=True, check=False)
    if res_build.returncode != 0:
        raise RuntimeError(f"lake build failed:\n{res_build.stdout}\n{res_build.stderr}")

    res_ax = subprocess.run(
        ["lake", "env", "lean", "AuditAxioms.lean"],
        cwd=lean_dir,
        capture_output=True,
        text=True,
        check=False,
    )
    if res_ax.returncode != 0:
        raise RuntimeError(f"AuditAxioms.lean failed:\n{res_ax.stdout}\n{res_ax.stderr}")
    out = res_ax.stdout + res_ax.stderr
    for banned in ("Classical.choice", "Lean.ofReduceBool", "sorryAx"):
        if banned in out:
            raise RuntimeError(f"Disallowed axiom {banned} found in Lean audit:\n{out}")
    for thm in EXPECTED_THEOREMS:
        if f"'{thm}'" not in out:
            raise RuntimeError(f"Missing theorem {thm} in AuditAxioms output")


def audit_certificates() -> int:
    certs = sorted((ROOT / "certificates").glob("*.json"))
    if len(certs) != 16:
        raise RuntimeError(f"Expected 16 canonical certificates, found {len(certs)}")
    for p in certs:
        data = json.loads(p.read_text(encoding="utf-8"))
        ok, msg, _ = verify_certificate(data)
        if not ok:
            raise RuntimeError(f"Certificate {p.name} FAILED: {msg}")
    return len(certs)


def write_manifest() -> int:
    files = collect_tracked_files()
    manifest: Dict[str, str] = {p.relative_to(ROOT).as_posix(): _sha256(p) for p in files}
    (ROOT / "SHA256_MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    return len(manifest)


def verify_manifest() -> int:
    mpath = ROOT / "SHA256_MANIFEST.json"
    if not mpath.exists():
        raise RuntimeError("SHA256_MANIFEST.json missing")
    expected: Dict[str, str] = json.loads(mpath.read_text(encoding="utf-8"))
    actual = {p.relative_to(ROOT).as_posix(): _sha256(p) for p in collect_tracked_files()}
    if set(expected.keys()) != set(actual.keys()):
        missing = sorted(set(expected) - set(actual))
        extra = sorted(set(actual) - set(expected))
        raise RuntimeError(f"Manifest file set mismatch (missing={missing}, extra={extra})")
    for k, digest in expected.items():
        if actual[k] != digest:
            raise RuntimeError(f"SHA-256 mismatch for {k}")
    return len(actual)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write-manifest", action="store_true")
    args = parser.parse_args()

    audit_zero_float_sources()
    print("[PASS] Zero-float source audit (src/)")

    audit_lean_kernel()
    print("[PASS] Lean 4.35.0 kernel: 18/18 theorems, 0 sorry, 0 Classical.choice")

    n_certs = audit_certificates()
    print(f"[PASS] Canonical certificates: {n_certs}/16 verified over exact discrete domains")

    rej, tot, fails = run_red_team_suite()
    if fails or rej != tot:
        raise RuntimeError(f"Red-team failures: {fails}")
    print(f"[PASS] Adversarial red-team suite: {rej}/{tot} forged payloads rejected")

    if args.write_manifest:
        n = write_manifest()
        print(f"[OK] Wrote SHA256_MANIFEST.json ({n} artifacts)")
    else:
        n = verify_manifest()
        print(f"[PASS] SHA-256 manifest integrity: {n}/{n} matched")


if __name__ == "__main__":
    main()
