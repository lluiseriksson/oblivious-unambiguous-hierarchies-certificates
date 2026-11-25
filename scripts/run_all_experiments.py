"""Generate all 16 canonical OUH-CERT-1.0 certificates and 4 exact datasets.

Author: Lluis Eriksson
License: MIT
"""

from __future__ import annotations

import json
from pathlib import Path
import sys
import time
from typing import Any, Dict, List, Set

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.ouh_certifier import SCHEMA_VERSION, verify_certificate
from src.ouh_exact import (
    all_bitstrings,
    cantor_pair,
    mahaney_extract_oup_witness,
    prefix_search_lex_max,
    simulate_loose_promise_tower,
)


def _write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2) + "\n", encoding="utf-8")


def _make_m1(cert_id: str, ref: str, bit_len: int, feasible: List[str]) -> Dict[str, Any]:
    a_n, trace = prefix_search_lex_max(set(feasible), bit_len)
    return {
        "schema_version": SCHEMA_VERSION,
        "cert_id": cert_id,
        "mode": "canonical_advice_ogtd_cert",
        "reference": ref,
        "payload": {
            "bit_len": bit_len,
            "feasible_encodings": feasible,
            "claimed_canonical_a_n": a_n,
            "claimed_prefix_queries": trace,
            "claimed_co_onp_accepted_count": 1,
        },
    }


def _make_m2(
    cert_id: str,
    ref: str,
    n: int,
    p: int,
    h: int,
    tally_set: List[int],
    acc_pairs: List[List[str]],
) -> Dict[str, Any]:
    pair_set = {(x, w) for x, w in acc_pairs}
    w_ext, bits = mahaney_extract_oup_witness(pair_set, p)
    return {
        "schema_version": SCHEMA_VERSION,
        "cert_id": cert_id,
        "mode": "mahaney_census_ouh_cert",
        "reference": ref,
        "payload": {
            "input_len": n,
            "witness_len": p,
            "tally_bound_h": h,
            "tally_oracle_set": tally_set,
            "claimed_census_cm": len(tally_set),
            "claimed_paired_checksum": cantor_pair(n, len(tally_set)),
            "accepted_pairs": acc_pairs,
            "claimed_slice_nonempty": len(acc_pairs) > 0,
            "claimed_extracted_witness": w_ext,
            "claimed_bit_queries": bits,
        },
    }


def _make_m3(
    cert_id: str,
    ref: str,
    depth: int,
    inputs: List[str],
    base_A0: Dict[str, bool],
    levels: List[Dict[str, object]],
    top_machine: Dict[str, Dict[str, object]],
) -> Dict[str, Any]:
    sim = simulate_loose_promise_tower(inputs, depth, base_A0, levels, top_machine)
    return {
        "schema_version": SCHEMA_VERSION,
        "cert_id": cert_id,
        "mode": "loose_promise_tower_cert",
        "reference": ref,
        "payload": {
            "depth": depth,
            "inputs": inputs,
            "base_A0": base_A0,
            "levels": levels,
            "top_machine": top_machine,
            "claimed_rounds": sim["rounds"],
            "claimed_every_round_adds_true_witness": True,
            "claimed_final_S": sim["final_S"],
            "claimed_decoder_matches": sim["decoder_matches_exact"],
            "claimed_true_outputs": sim["true_outputs"],
        },
    }


def _build_depth2_tower(out_accepts_spurious: bool = False) -> Dict[str, Any]:
    # Level 0: A0 = {"b0": False, "b1": True}
    # Level 1 (prOUP^{A0}): queries q1_yes (promised YES), q1_no (promised NO), q1_oop (out-of-promise!)
    #   witnesses: ["w1_bad", "w1_true"] (ordered so "w1_bad" comes before "w1_true"!)
    #   On q1_yes: V1(q1_yes, w1_true) = A0(b1) = True; V1(q1_yes, w1_bad) = False
    #   On q1_no: V1(q1_no, *) = False
    #   On q1_oop (out of promise!): V1(q1_oop, w1_bad) = True if out_accepts_spurious else False!
    # Level 2 (prOUP^{Pi_1}): queries q2_yes (promised YES), q2_no (promised NO), q2_oop (out-of-promise!)
    #   witnesses: ["w2_bad", "w2_true"]
    #   On q2_yes: V2(q2_yes, w2_true) queries q1_yes (acc iff q1_yes == True); V2(q2_yes, w2_bad) = False
    #   On q2_no: V2(q2_no, w2_true) queries q1_no (acc iff q1_no == True -> False); V2(q2_no, w2_bad) queries q1_yes (acc iff q1_yes == False -> spurious until w1_true added!)
    #   On q2_oop: V2(q2_oop, *) = False
    base_A0 = {"b0": False, "b1": True}
    v1 = {
        "q1_yes|w1_bad": {"query": None, "acc_if_0": False, "acc_if_1": False},
        "q1_yes|w1_true": {"query": "b1", "acc_if_0": False, "acc_if_1": True},
        "q1_no|w1_bad": {"query": "b0", "acc_if_0": False, "acc_if_1": True},
        "q1_no|w1_true": {"query": "b0", "acc_if_0": False, "acc_if_1": True},
        "q1_oop|w1_bad": {"query": None, "acc_if_0": out_accepts_spurious, "acc_if_1": out_accepts_spurious},
        "q1_oop|w1_true": {"query": "b1", "acc_if_0": False, "acc_if_1": True},
    }
    v2 = {
        "q2_yes|w2_bad": {"query": None, "acc_if_0": False, "acc_if_1": False},
        "q2_yes|w2_true": {"query": "q1_yes", "acc_if_0": False, "acc_if_1": True},
        "q2_no|w2_bad": {"query": "q1_yes", "acc_if_0": True, "acc_if_1": False},
        "q2_no|w2_true": {"query": "q1_no", "acc_if_0": False, "acc_if_1": True},
        "q2_oop|w2_bad": {"query": "q1_oop", "acc_if_0": False, "acc_if_1": True},
        "q2_oop|w2_true": {"query": None, "acc_if_0": False, "acc_if_1": False},
    }
    levels = [
        {
            "queries": ["q1_yes", "q1_no", "q1_oop"],
            "witnesses": ["w1_bad", "w1_true"],
            "promise_yes": ["q1_yes"],
            "promise_no": ["q1_no"],
            "true_witness": "w1_true",
            "verifier": v1,
        },
        {
            "queries": ["q2_yes", "q2_no", "q2_oop"],
            "witnesses": ["w2_bad", "w2_true"],
            "promise_yes": ["q2_yes"],
            "promise_no": ["q2_no"],
            "true_witness": "w2_true",
            "verifier": v2,
        },
    ]
    top_machine = {
        "x0": {"query": "q2_yes", "out_if_0": False, "out_if_1": True},
        "x1": {"query": "q2_no", "out_if_0": False, "out_if_1": True},
        "x2": {"query": "q2_oop", "out_if_0": True, "out_if_1": True},  # loose: independent of oop answer!
    }
    return {"depth": 2, "inputs": ["x0", "x1", "x2"], "base_A0": base_A0, "levels": levels, "top_machine": top_machine}


def _build_depth3_tower() -> Dict[str, Any]:
    base_A0 = {"b0": False, "b1": True}
    v1 = {
        "q1_yes|w1_alt": {"query": None, "acc_if_0": False, "acc_if_1": False},
        "q1_yes|w1_ok": {"query": "b1", "acc_if_0": False, "acc_if_1": True},
        "q1_no|w1_alt": {"query": "b0", "acc_if_0": False, "acc_if_1": True},
        "q1_no|w1_ok": {"query": "b0", "acc_if_0": False, "acc_if_1": True},
    }
    v2 = {
        "q2_yes|w2_alt": {"query": None, "acc_if_0": False, "acc_if_1": False},
        "q2_yes|w2_ok": {"query": "q1_yes", "acc_if_0": False, "acc_if_1": True},
        "q2_no|w2_alt": {"query": "q1_yes", "acc_if_0": True, "acc_if_1": False},
        "q2_no|w2_ok": {"query": "q1_no", "acc_if_0": False, "acc_if_1": True},
    }
    v3 = {
        "q3_yes|w3_alt": {"query": None, "acc_if_0": False, "acc_if_1": False},
        "q3_yes|w3_ok": {"query": "q2_yes", "acc_if_0": False, "acc_if_1": True},
        "q3_no|w3_alt": {"query": "q2_yes", "acc_if_0": True, "acc_if_1": False},
        "q3_no|w3_ok": {"query": "q2_no", "acc_if_0": False, "acc_if_1": True},
    }
    levels = [
        {"queries": ["q1_yes", "q1_no"], "witnesses": ["w1_alt", "w1_ok"], "promise_yes": ["q1_yes"], "promise_no": ["q1_no"], "true_witness": "w1_ok", "verifier": v1},
        {"queries": ["q2_yes", "q2_no"], "witnesses": ["w2_alt", "w2_ok"], "promise_yes": ["q2_yes"], "promise_no": ["q2_no"], "true_witness": "w2_ok", "verifier": v2},
        {"queries": ["q3_yes", "q3_no"], "witnesses": ["w3_alt", "w3_ok"], "promise_yes": ["q3_yes"], "promise_no": ["q3_no"], "true_witness": "w3_ok", "verifier": v3},
    ]
    top_machine = {
        "x0": {"query": "q3_yes", "out_if_0": False, "out_if_1": True},
        "x1": {"query": "q3_no", "out_if_0": False, "out_if_1": True},
    }
    return {"depth": 3, "inputs": ["x0", "x1"], "base_A0": base_A0, "levels": levels, "top_machine": top_machine}


def build_canonical_certificates() -> List[Dict[str, Any]]:
    certs: List[Dict[str, Any]] = []

    # MODE 1: Lemma 3.1 Canonical Lex-Max Advice & co-ONP Tester (4 certs)
    certs.append(_make_m1("m1_canonical_advice_len4_sparse", "Hirsch (2026) Lemma 3.1 & Cor. 3.2 (L=4)", 4, ["0010", "0101", "1010", "1001"]))
    certs.append(_make_m1("m1_canonical_advice_len6_dense", "Hirsch (2026) Lemma 3.1 & Cor. 3.2 (L=6)", 6, ["000111", "011010", "101101", "110010", "110011", "100001"]))
    certs.append(_make_m1("m1_canonical_advice_len8_max", "Hirsch (2026) Lemma 3.1 prefix search (L=8)", 8, ["01010101", "10101010", "11011011", "11011100", "00110011"]))
    certs.append(_make_m1("m1_canonical_advice_singleton", "Hirsch (2026) Lemma 3.1 unique feasible run (L=5)", 5, ["01101"]))

    # MODE 2: Lemma 2.8 Mahaney Census & Theorem 4.1 Bit Extraction (4 certs)
    certs.append(_make_m2("m2_mahaney_ouh_nonempty_n3_p4", "Hirsch (2026) Lem. 2.8 & Thm. 4.1 (nonempty slice)", 3, 4, 12, [0, 2, 5, 9, 11], [["001", "1011"], ["010", "1011"], ["111", "1011"]]))
    certs.append(_make_m2("m2_mahaney_ouh_empty_slice_zero", "Hirsch (2026) Thm. 4.1 empty slice -> 0^{p(n)}", 3, 4, 10, [1, 3, 7], []))
    certs.append(_make_m2("m2_mahaney_ouh_full_tally_n4_p5", "Hirsch (2026) Lem. 2.8 & Thm. 4.1 (n=4, p=5)", 4, 5, 16, [0, 4, 8, 12, 16], [["0000", "11010"], ["1010", "11010"], ["1111", "11010"], ["0101", "11010"]]))
    certs.append(_make_m2("m2_mahaney_ouh_all_ones_witness", "Hirsch (2026) Thm. 4.1 all-ones oblivious witness", 2, 6, 8, [2, 6], [["01", "111111"], ["10", "111111"]]))

    # MODE 3: Theorem 5.1 Loose Promise-Oracle Tower & Round Termination (4 certs)
    # 3a. Depth-1 prOUP tower with out-of-promise query
    t1_base = {"b0": False, "b1": True}
    t1_v1 = {
        "q1_yes|w_bad": {"query": None, "acc_if_0": False, "acc_if_1": False},
        "q1_yes|w_ok": {"query": "b1", "acc_if_0": False, "acc_if_1": True},
        "q1_no|w_bad": {"query": "b0", "acc_if_0": False, "acc_if_1": True},
        "q1_no|w_ok": {"query": "b0", "acc_if_0": False, "acc_if_1": True},
        "q1_oop|w_bad": {"query": None, "acc_if_0": True, "acc_if_1": True},
        "q1_oop|w_ok": {"query": None, "acc_if_0": False, "acc_if_1": False},
    }
    t1_lvls = [{"queries": ["q1_yes", "q1_no", "q1_oop"], "witnesses": ["w_bad", "w_ok"], "promise_yes": ["q1_yes"], "promise_no": ["q1_no"], "true_witness": "w_ok", "verifier": t1_v1}]
    t1_top = {"x0": {"query": "q1_yes", "out_if_0": False, "out_if_1": True}, "x1": {"query": "q1_no", "out_if_0": False, "out_if_1": True}, "x2": {"query": "q1_oop", "out_if_0": False, "out_if_1": False}}
    certs.append(_make_m3("m3_loose_tower_depth1_oop", "Hirsch (2026) Theorem 5.1 depth-1 loose promise tower", 1, ["x0", "x1", "x2"], t1_base, t1_lvls, t1_top))

    t2a = _build_depth2_tower(out_accepts_spurious=False)
    certs.append(_make_m3("m3_loose_tower_depth2_clean", "Hirsch (2026) Theorem 5.1 depth-2 loose promise tower", **t2a))

    t2b = _build_depth2_tower(out_accepts_spurious=True)
    certs.append(_make_m3("m3_loose_tower_depth2_spurious_oop", "Hirsch (2026) Theorem 5.1 depth-2 with spurious out-of-promise witness", **t2b))

    t3 = _build_depth3_tower()
    certs.append(_make_m3("m3_loose_tower_depth3_descent", "Hirsch (2026) Theorem 5.1 depth-3 inductive tower descent", **t3))

    # MODE 4: Section 6 Theorems (4 certs: 2 dot_op_collapse, 1 single_loose_query, 1 soup_intersection)
    def _make_dot_op(cert_id: str, ref: str, n: int, p: int, q: int, w_n: str, v_N: str, L_map: Dict[str, bool]) -> Dict[str, Any]:
        xs, ws, vs = all_bitstrings(n), all_bitstrings(p), all_bitstrings(q)
        v_map = {}
        for x in xs:
            for w in ws:
                in_R = L_map[x] and (w == w_n)
                for v in vs:
                    v_map[f"{x}|{w}|{v}"] = (not in_R) and (v == v_N)
        z_n, p0, p1 = "0" * n, "0" * p, "1" * p
        return {
            "schema_version": SCHEMA_VERSION,
            "cert_id": cert_id,
            "mode": "dot_op_single_query_soup_cert",
            "reference": ref,
            "payload": {
                "submode": "dot_op_collapse",
                "input_len": n,
                "outer_w_len": p,
                "inner_v_len": q,
                "outer_witness_w_n": w_n,
                "inner_witness_v_N": v_N,
                "language_L": L_map,
                "inner_verifier_Rbar": v_map,
                "claimed_probe_refutes_0p": any(v_map[f"{z_n}|{p0}|{v}"] for v in vs),
                "claimed_probe_refutes_1p": any(v_map[f"{z_n}|{p1}|{v}"] for v in vs),
                "claimed_unique_pair_ok": True,
            },
        }

    # 4a. Dot-op collapse where 0^n in L and w_n = 00 -> probe 11 refutes R!
    certs.append(_make_dot_op("m4_dot_op_collapse_probe_1p", "Hirsch (2026) Theorem 6.2 (0^n in L, w_n=00, 1^p refutes)", 2, 2, 2, "00", "10", {"00": True, "01": False, "10": True, "11": False}))
    # 4b. Dot-op collapse where 0^n not in L -> both 0^p and 1^p refute R!
    certs.append(_make_dot_op("m4_dot_op_collapse_both_probes", "Hirsch (2026) Theorem 6.2 & Cor. 6.3 (0^n not in L)", 2, 2, 2, "10", "01", {"00": False, "01": True, "10": False, "11": True}))

    # 4c. Single loose query guardedness & input-tagging (Lemma 6.4 & Theorem 6.5)
    certs.append(
        {
            "schema_version": SCHEMA_VERSION,
            "cert_id": "m4_single_loose_query_tagging",
            "mode": "dot_op_single_query_soup_cert",
            "reference": "Hirsch (2026) Lemma 6.4 & Theorem 6.5 (OUP^{prOUP[1]} = OUP^{OUP[1]})",
            "payload": {
                "submode": "single_loose_query",
                "inputs": ["x0", "x1", "x2"],
                "witnesses": ["w0", "w1"],
                "true_witness": "w1",
                "language_L": {"x0": True, "x1": False, "x2": True},
                "promise_yes": ["q_yes"],
                "promise_no": ["q_no"],
                "out_of_promise": ["q_oop1", "q_oop2"],
                "query_map": {
                    "x0|w0": "q_oop1",
                    "x0|w1": "q_yes",
                    "x1|w0": "q_oop2",
                    "x1|w1": "q_no",
                    "x2|w0": "q_oop1",
                    "x2|w1": "q_yes",
                },
                "verifier_if_0": {
                    "x0|w0": False,
                    "x0|w1": False,
                    "x1|w0": False,
                    "x1|w1": False,
                    "x2|w0": False,
                    "x2|w1": False,
                },
                "verifier_if_1": {
                    "x0|w0": False,
                    "x0|w1": True,
                    "x1|w0": False,
                    "x1|w1": True,
                    "x2|w0": False,
                    "x2|w1": True,
                },
                "claimed_mattering_set_size": 3,
                "claimed_tagged_A_size": 2,
            },
        }
    )

    # 4d. SOUP = OUP cap co-OUP (Proposition 6.6)
    xs_s = all_bitstrings(3)
    ws_s = all_bitstrings(2)
    L_s = {x: (x.count("1") % 2 == 1) for x in xs_s}  # 000 not in L -> b*=0, w*=wZ="11"
    wY, wZ = "01", "11"
    Y_s = {f"{x}|{w}": (L_s[x] and w == wY) for x in xs_s for w in ws_s}
    Z_s = {f"{x}|{w}": ((not L_s[x]) and w == wZ) for x in xs_s for w in ws_s}
    certs.append(
        {
            "schema_version": SCHEMA_VERSION,
            "cert_id": "m4_soup_equals_oup_inter_co_oup",
            "mode": "dot_op_single_query_soup_cert",
            "reference": "Hirsch (2026) Proposition 6.6 (SOUP = OUP cap co-OUP)",
            "payload": {
                "submode": "soup_intersection",
                "input_len": 3,
                "witness_len": 2,
                "language_L": L_s,
                "witness_Y": wY,
                "witness_Z": wZ,
                "verifier_Y": Y_s,
                "verifier_Z": Z_s,
                "claimed_soup_bit": 0,
                "claimed_soup_witness": wZ,
            },
        }
    )

    return certs


def main() -> None:
    cert_dir = ROOT / "certificates"
    data_dir = ROOT / "data"
    cert_dir.mkdir(parents=True, exist_ok=True)
    data_dir.mkdir(parents=True, exist_ok=True)

    certs = build_canonical_certificates()
    replay_rows: List[Dict[str, Any]] = []
    for cert in certs:
        _write_json(cert_dir / f"{cert['cert_id']}.json", cert)
        t0 = time.perf_counter_ns()
        ok, msg, summary = verify_certificate(cert)
        dt_ns = time.perf_counter_ns() - t0
        if not ok:
            raise RuntimeError(f"Canonical cert {cert['cert_id']} FAILED: {msg}")
        replay_rows.append(
            {
                "cert_id": cert["cert_id"],
                "mode": cert["mode"],
                "verified": ok,
                "verify_ns": dt_ns,
                "summary": summary,
            }
        )
    _write_json(data_dir / "certificate_replay_summary.json", {"certificates": replay_rows})

    # Dataset 1: Prefix-search query complexity & co-ONP uniqueness across bit lengths L=2..8
    exp1_rows = []
    for L in range(2, 9):
        # Construct structured feasible subset of size 3 * 2^(L-2)
        feas = [s for s in all_bitstrings(L) if s[0] == "0" or s[-1] == "0"]
        a_n, trace = prefix_search_lex_max(set(feas), L)
        exp1_rows.append(
            {
                "bit_len": L,
                "universe_size": 1 << L,
                "feasible_count": len(feas),
                "prefix_queries": len(trace),
                "canonical_a_n": a_n,
                "co_onp_accepted": 1,
            }
        )
    _write_json(data_dir / "exp1_canonical_advice_scaling.json", {"rows": exp1_rows})

    # Dataset 2: Loose promise-tower round-bound vs actual rounds across depths d=1..3
    exp2_rows = [r["summary"] for r in replay_rows if r["mode"] == "loose_promise_tower_cert"]
    _write_json(data_dir / "exp2_loose_tower_rounds.json", {"rows": exp2_rows})

    # Dataset 3: Cantor pairing bijectivity & Mahaney census summary
    exp3_rows = []
    for h in [4, 8, 12, 16, 24, 32]:
        pairs: Set[int] = {cantor_pair(a, b) for a in range(h + 1) for b in range(h + 1)}
        exp3_rows.append(
            {
                "bound_h": h,
                "pairs_tested": (h + 1) * (h + 1),
                "distinct_codes": len(pairs),
                "max_code": max(pairs),
            }
        )
    _write_json(data_dir / "exp3_cantor_census_injectivity.json", {"rows": exp3_rows})

    # Dataset 4: Section 6 submodes summary
    exp4_rows = [r["summary"] for r in replay_rows if r["mode"] == "dot_op_single_query_soup_cert"]
    _write_json(data_dir / "exp4_sec6_collapse_summary.json", {"rows": exp4_rows})

    total_ms = sum(r["verify_ns"] for r in replay_rows) / 1_000_000
    min_ms = min(r["verify_ns"] for r in replay_rows) / 1_000_000
    max_ms = max(r["verify_ns"] for r in replay_rows) / 1_000_000
    print(f"Generated and verified {len(certs)}/16 canonical certificates.")
    print(f"Latency: min={min_ms:.3f} ms, max={max_ms:.3f} ms, total={total_ms:.2f} ms")


if __name__ == "__main__":
    main()
