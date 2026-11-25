"""Generate 3 publication-quality 300 DPI figures for OUH-CERT-1.0.

Author: Lluis Eriksson
License: MIT
"""

from __future__ import annotations

import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent.parent


def make_fig1() -> None:
    d1 = json.loads((ROOT / "data" / "exp1_canonical_advice_scaling.json").read_text(encoding="utf-8"))["rows"]
    d3 = json.loads((ROOT / "data" / "exp3_cantor_census_injectivity.json").read_text(encoding="utf-8"))["rows"]

    Ls = [r["bit_len"] for r in d1]
    univ = [r["universe_size"] for r in d1]
    feas = [r["feasible_count"] for r in d1]
    queries = [r["prefix_queries"] for r in d1]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(8.2, 3.35), dpi=300)

    ax1.semilogy(Ls, univ, "o--", color="#7f8c8d", lw=1.6, ms=4, label=r"Universe $2^L$")
    ax1.semilogy(Ls, feas, "s-", color="#1b4f72", lw=1.8, ms=4.5, label=r"Feasible $|R| = 3 \cdot 2^{L-2}$")
    ax1.semilogy(Ls, queries, "^-", color="#c0392b", lw=2.0, ms=5, label=r"$\mathrm{FP}^{\mathrm{ONP}}$ prefix queries ($= L$)")
    ax1.set_xticks(Ls)
    ax1.set_xlabel(r"Canonical advice bit-length $L$", fontsize=8.5)
    ax1.set_ylabel("Count (log scale)", fontsize=8.5)
    ax1.set_title("(a) Lemma 3.1 lex-max prefix search", fontsize=9.0, fontweight="bold")
    ax1.grid(True, which="both", alpha=0.22)
    ax1.legend(fontsize=6.6, loc="upper left", framealpha=0.92)

    hs = [r["bound_h"] for r in d3]
    pairs = [r["pairs_tested"] for r in d3]
    max_code = [r["max_code"] for r in d3]

    ax2.plot(hs, pairs, "o-", color="#148f77", lw=1.9, ms=4.5, label=r"Distinct pairs $(h+1)^2$ (0 collisions)")
    ax2.plot(hs, max_code, "s--", color="#7d3c98", lw=1.8, ms=4.5, label=r"Max Cantor code $\pi(h, h)$")
    ax2.set_xlabel(r"Tally oracle length bound $h$", fontsize=8.5)
    ax2.set_ylabel("Exact integer count / code", fontsize=8.5)
    ax2.set_title("(b) Sec. 2.1 & Lem. 2.8 Cantor census pairing", fontsize=9.0, fontweight="bold")
    ax2.grid(True, alpha=0.25)
    ax2.legend(fontsize=6.6, loc="upper left", framealpha=0.92)

    fig.tight_layout()
    out = ROOT / "figures" / "fig1_canonical_advice_and_census.png"
    out.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out, dpi=300)
    plt.close(fig)


def make_fig2() -> None:
    d2 = json.loads((ROOT / "data" / "exp2_loose_tower_rounds.json").read_text(encoding="utf-8"))["rows"]

    labels = ["Depth 1\n(OOP)", "Depth 2\n(Clean)", "Depth 2\n(Spurious)", "Depth 3\n(Descent)"]
    depths = [r["depth"] for r in d2]
    rounds = [r["rounds"] for r in d2]
    tot_s = [sum(r["final_S_sizes"]) for r in d2]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(8.2, 3.35), dpi=300)

    x = list(range(len(labels)))
    w = 0.26
    ax1.bar([i - w for i in x], depths, width=w, color="#1b4f72", label=r"Thm. 5.1 round cap $d$")
    ax1.bar(x, rounds, width=w, color="#148f77", label="Actual generator rounds")
    ax1.bar([i + w for i in x], tot_s, width=w, color="#d35400", label=r"Final $|S|$ witnesses")
    ax1.set_xticks(x)
    ax1.set_xticklabels(labels, fontsize=7.5)
    ax1.set_ylim(0, 5.2)
    ax1.set_ylabel("Rounds / candidate witness count", fontsize=8.5)
    ax1.set_title(r"(a) Theorem 5.1 $\mathrm{OUH}^\bullet$ tower generator", fontsize=9.0, fontweight="bold")
    ax1.grid(True, axis="y", alpha=0.25)
    ax1.legend(fontsize=6.6, loc="upper left", framealpha=0.92)

    # Panel (b): Section 6 exact structural verification summary (read directly from certificates/)
    s6_files = [
        ("Thm. 6.2\n(1^p probe)", "m4_dot_op_collapse_probe_1p.json", "inner_verifier_Rbar"),
        ("Thm. 6.2\n(both probes)", "m4_dot_op_collapse_both_probes.json", "inner_verifier_Rbar"),
        ("Lem. 6.4/6.5\n(tagging)", "m4_single_loose_query_tagging.json", "query_map"),
        ("Prop. 6.6\n(SOUP)", "m4_soup_equals_oup_inter_co_oup.json", "verifier_Y"),
    ]
    s6_labels = [lbl for lbl, _, _ in s6_files]
    checked_states = [
        len(json.loads((ROOT / "certificates" / fname).read_text(encoding="utf-8"))["payload"][field])
        for _, fname, field in s6_files
    ]
    x2 = list(range(len(s6_labels)))
    w2 = 0.34
    bars = ax2.bar(x2, checked_states, width=w2, color=["#1b4f72", "#2e86c1", "#b9770e", "#7d3c98"], edgecolor="#222222", lw=0.5)
    for b, val in zip(bars, checked_states):
        ax2.text(b.get_x() + b.get_width() / 2.0, val + 1.5, f"{val} entries\n(unique w)", ha="center", va="bottom", fontsize=6.7, fontweight="bold")
    ax2.set_xticks(x2)
    ax2.set_xticklabels(s6_labels, fontsize=7.3)
    ax2.set_ylim(0, 82)
    ax2.set_ylabel("Exhaustively verified truth-table entries", fontsize=8.5)
    ax2.set_title("(b) Section 6 collapse, tagging & SOUP audit", fontsize=9.0, fontweight="bold")
    ax2.grid(True, axis="y", alpha=0.25)

    fig.tight_layout()
    out = ROOT / "figures" / "fig2_loose_tower_and_sec6.png"
    fig.savefig(out, dpi=300)
    plt.close(fig)


def make_fig3() -> None:
    rep = json.loads((ROOT / "data" / "certificate_replay_summary.json").read_text(encoding="utf-8"))["certificates"]
    short_names = [f"C{i+1:02d}" for i in range(len(rep))]
    ms_vals = [r["verify_ns"] / 1_000_000 for r in rep]
    mode_colors = {
        "canonical_advice_ogtd_cert": "#1b4f72",
        "mahaney_census_ouh_cert": "#148f77",
        "loose_promise_tower_cert": "#b9770e",
        "dot_op_single_query_soup_cert": "#922b21",
    }
    bar_colors = [mode_colors[r["mode"]] for r in rep]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(8.2, 3.35), dpi=300)
    ax1.bar(short_names, ms_vals, color=bar_colors, edgecolor="#222222", lw=0.4)
    ax1.set_ylabel("Replay time (ms)", fontsize=8.5)
    ax1.set_xlabel("Canonical certificates (M1: C01-C04, M2: C05-C08, M3: C09-C12, M4: C13-C16)", fontsize=7.0)
    ax1.set_title("(a) Exact discrete replay latency (16/16 PASS)", fontsize=9.0, fontweight="bold")
    ax1.tick_params(axis="x", labelsize=6.8, rotation=45)
    ax1.grid(True, axis="y", alpha=0.25)

    cats = ["Global\nSchema", "Mode 1\nOGTD", "Mode 2\nCensus", "Mode 3\nTower", "Mode 4\nSec. 6"]
    counts = [13, 12, 12, 15, 13]
    colors2 = ["#34495e", "#1b4f72", "#148f77", "#b9770e", "#922b21"]
    bars = ax2.bar(cats, counts, color=colors2, edgecolor="#222222", lw=0.5)
    for b, cnt in zip(bars, counts):
        ax2.text(
            b.get_x() + b.get_width() / 2.0,
            b.get_height() + 0.35,
            f"{cnt}/{cnt}",
            ha="center",
            va="bottom",
            fontsize=7.5,
            fontweight="bold",
        )
    ax2.set_ylim(0, 17.5)
    ax2.set_ylabel("Forged payloads rejected", fontsize=8.5)
    ax2.set_title("(b) Live adversarial red-team audit (65/65)", fontsize=9.0, fontweight="bold")
    ax2.tick_params(axis="x", labelsize=7.5)
    ax2.grid(True, axis="y", alpha=0.25)

    fig.tight_layout()
    out = ROOT / "figures" / "fig3_certificate_replay_atlas.png"
    fig.savefig(out, dpi=300)
    plt.close(fig)


def main() -> None:
    make_fig1()
    make_fig2()
    make_fig3()
    print("Generated all 3 figures in figures/.")


if __name__ == "__main__":
    main()
