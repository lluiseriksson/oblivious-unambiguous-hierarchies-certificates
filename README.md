# Certified Verification of Input-Oblivious Unambiguous Hierarchies

[![License: MIT](https://img.shields.io/badge/Code%20%26%20Lean-MIT-blue.svg)](LICENSE)
[![Paper License: CC-BY-4.0](https://img.shields.io/badge/Paper-CC--BY--4.0-green.svg)](paper/main.tex)

**Author:** Lluis Eriksson

Machine-checked **Lean 4.35.0** formalization and zero-floating-point exact finite-combinatorial certificate audit (`OUH-CERT-1.0`) for **Edward A. Hirsch** ([arXiv:2611.33126](https://arxiv.org/abs/2611.33126), Nov 24, 2026), *"A note on input-oblivious unambiguous hierarchies"*.

---

## Key Verified Artifacts

| Artifact | Verification Metric | Result |
| :--- | :--- | :--- |
| **Lean 4.35.0 Kernel** (`lean/ObliviousUnambiguous.lean`) | 18 theorems, zero `sorry`, zero warnings, zero `Classical.choice` | **18 / 18 PASS** (`8` `none`, `4` `[propext]`, `6` `[propext, Quot.sound]`) |
| **Exact Discrete Verifier** (`src/ouh_certifier.py`) | Zero `float()`, `math.`, or `numpy`; 4-mode `OUH-CERT-1.0` | **16 / 16 PASS** (`0.033–0.210 ms`, total `1.64 ms`) |
| **Adversarial Red-Team Suite** (`tests/test_suite.py`) | 65 live forged payloads (13 global + 52 domain) | **65 / 65 REJECTED** |
| **SHA-256 Integrity Manifest** (`SHA256_MANIFEST.json`) | Full deterministic replay check (`scripts/verify_all.py`) | **40 / 40 MATCH** |
| **Manuscript** (`paper/main.pdf`) | 3 pages, 3 publication figures (`300 DPI`) | **0 warnings, 0 overfulls** |

---

## Four Certificate Modes (`OUH-CERT-1.0`)

1. **`canonical_advice_ogtd_cert` (Mode 1 — Lemma 3.1 & Corollary 3.2):** Executes exact $L$-step $\mathsf{FP}^{\mathsf{ONP}}$ prefix search over finite feasible run encodings, verifies lex-max canonical advice $a_n$, and certifies unique acceptance ($|\mathrm{Acc}_T| = 1$) by the $\mathsf{co}\text{-}\mathsf{ONP}$ tester.
2. **`mahaney_census_ouh_cert` (Mode 2 — Lemma 2.8 & Theorem 4.1):** Verifies Mahaney census checksum $c_m$, Cantor pairing $\pi(n, c_m)$ and query-code injectivity, strict oblivious unambiguity across accepted $(x, w)$ pairs, and bit-by-bit tally witness extraction (including empty-slice $0^p$ default).
3. **`loose_promise_tower_cert` (Mode 3 — Theorem 5.1):** Enumerates all consistent oracles across depths $1..3$ to verify loose $\mathsf{prOUP}$ semantics and out-of-promise invariance, runs Hirsch's exact round-by-round $\mathsf{FP}^{\mathsf{NP}}$ generator from $S^{(0)} = \emptyset$, verifies every round adds a missing true witness within $\le d$ rounds, and certifies $D(x, S^*) = M^{A_d}(x)$.
4. **`dot_op_single_query_soup_cert` (Mode 4 — Section 6):** Exhaustively certifies truth tables across three submodes: Theorem 6.2/Corollary 6.3 dot-operator collapse (`dot_op_collapse`), Lemma 6.4/Theorem 6.5 single-loose-query guardedness and input-tagging (`single_loose_query`), and Proposition 6.6 $\mathsf{SOUP} = \mathsf{OUP} \cap \mathsf{co}\text{-}\mathsf{OUP}$ (`soup_intersection`).

---

## Quick Reproduction

```bash
cd lean && lake build && lake env lean AuditAxioms.lean && cd ..
python scripts/run_all_experiments.py
python scripts/make_figures.py
python scripts/verify_all.py
```

---

## Licenses & Transparency Disclosure

- **Code, Lean proofs, certificates, and scripts:** [MIT License](LICENSE).
- **Manuscript (`paper/main.tex`, `paper/main.pdf`) and figures:** CC-BY-4.0.
- **AI Assistance Disclosure:** Prepared by sole author Lluis Eriksson with AI coding, formalization, and drafting assistance from Google Antigravity; all Lean proofs, exact discrete certificates, and adversarial tests were independently compiled and machine-verified locally.
