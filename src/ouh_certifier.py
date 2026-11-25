"""Exact finite-combinatorial four-mode certificate verifier for OUH-CERT-1.0.

Verifies input-oblivious unambiguous hierarchy certificates for Edward A. Hirsch,
"A note on input-oblivious unambiguous hierarchies" (arXiv:2611.33126, Nov 2026).

Strictly zero floating-point operations (uses exact int, bool, str only).
Author: Lluis Eriksson
License: MIT
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Set, Tuple

from src.ouh_exact import (
    all_bitstrings,
    cantor_pair,
    co_onp_tester_accepted,
    is_bitstring,
    mahaney_extract_oup_witness,
    prefix_search_lex_max,
    simulate_loose_promise_tower,
)

SCHEMA_VERSION = "OUH-CERT-1.0"
MAX_BIT_LEN = 2048
MAX_JSON_DEPTH = 32
MAX_ID_LEN = 128

VALID_MODES = {
    "canonical_advice_ogtd_cert",
    "mahaney_census_ouh_cert",
    "loose_promise_tower_cert",
    "dot_op_single_query_soup_cert",
}


class CertError(ValueError):
    """Raised when a certificate violates schema, typing, or mathematical invariants."""


def _assert_strict_json_types(obj: Any, path: str = "root", depth: int = 0) -> None:
    if depth > MAX_JSON_DEPTH:
        raise CertError(f"{path}: JSON nesting depth exceeds {MAX_JSON_DEPTH}")
    if obj is None or type(obj) in (bool, int, str):
        return
    if type(obj) is list:
        for i, item in enumerate(obj):
            _assert_strict_json_types(item, f"{path}[{i}]", depth + 1)
        return
    if type(obj) is dict:
        for k, v in obj.items():
            if type(k) is not str:
                raise CertError(f"{path}: non-string dict key")
            _assert_strict_json_types(v, f"{path}.{k}", depth + 1)
        return
    raise CertError(f"{path}: disallowed type {type(obj).__name__} (non-exact types forbidden)")


def _require_exact_keys(d: Any, expected: set[str], label: str) -> Dict[str, Any]:
    if type(d) is not dict:
        raise CertError(f"{label}: expected dict")
    keys = set(d.keys())
    if keys != expected:
        missing = sorted(expected - keys)
        extra = sorted(keys - expected)
        raise CertError(f"{label}: key mismatch (missing={missing}, extra={extra})")
    return d


def _parse_bool(v: Any, label: str) -> bool:
    if type(v) is not bool:
        raise CertError(f"{label}: expected bool, got {type(v).__name__}")
    return v


def _parse_int(v: Any, label: str, lo: Optional[int] = None, hi: Optional[int] = None) -> int:
    if type(v) is not int:
        raise CertError(f"{label}: expected int, got {type(v).__name__}")
    if v.bit_length() > MAX_BIT_LEN:
        raise CertError(f"{label}: integer exceeds {MAX_BIT_LEN} bits")
    if lo is not None and v < lo:
        raise CertError(f"{label}: {v} < {lo}")
    if hi is not None and v > hi:
        raise CertError(f"{label}: {v} > {hi}")
    return v


def _parse_id_str(v: Any, label: str) -> str:
    if type(v) is not str or not v or len(v) > MAX_ID_LEN:
        raise CertError(f"{label}: expected non-empty string of length <= {MAX_ID_LEN}")
    if any(ord(ch) < 32 or ord(ch) == 127 for ch in v):
        raise CertError(f"{label}: ASCII control characters disallowed")
    return v


def _parse_bitstr(v: Any, bit_len: int, label: str) -> str:
    if not is_bitstring(v, bit_len):
        raise CertError(f"{label}: expected bitstring of length {bit_len}, got {v!r}")
    return str(v)


def _verify_mode1(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 1: Lemma 3.1 & Corollary 3.2 canonical lex-max advice, prefix search, & co-ONP tester."""
    _require_exact_keys(
        payload,
        {
            "bit_len",
            "feasible_encodings",
            "claimed_canonical_a_n",
            "claimed_prefix_queries",
            "claimed_co_onp_accepted_count",
        },
        "mode1.payload",
    )
    L = _parse_int(payload["bit_len"], "bit_len", 2, 8)
    raw_feas = payload["feasible_encodings"]
    if type(raw_feas) is not list or not raw_feas or len(raw_feas) > (1 << L):
        raise CertError("feasible_encodings: expected non-empty list of distinct bitstrings")
    feasible: Set[str] = set()
    for i, s in enumerate(raw_feas):
        bs = _parse_bitstr(s, L, f"feasible_encodings[{i}]")
        if bs in feasible:
            raise CertError(f"feasible_encodings[{i}]: duplicate bitstring {bs!r}")
        feasible.add(bs)

    a_n, trace = prefix_search_lex_max(feasible, L)
    expected_lex_max = max(feasible)
    if a_n != expected_lex_max:
        raise CertError("Internal prefix-search mismatch with lex-max")
    acc_t = co_onp_tester_accepted(feasible, L)
    if acc_t != [a_n]:
        raise CertError(f"co-ONP tester failed uniqueness: accepted {acc_t}")

    claimed_a = _parse_bitstr(payload["claimed_canonical_a_n"], L, "claimed_canonical_a_n")
    if claimed_a != a_n:
        raise CertError(f"claimed_canonical_a_n={claimed_a!r} != {a_n!r}")

    claimed_q = payload["claimed_prefix_queries"]
    if type(claimed_q) is not list or len(claimed_q) != L:
        raise CertError(f"claimed_prefix_queries: expected {L} prefix-search steps")
    for j, step in enumerate(claimed_q):
        _require_exact_keys(step, {"step", "probe", "oracle_answer", "bit"}, f"claimed_prefix_queries[{j}]")
        if _parse_int(step["step"], f"step[{j}]", 0, L - 1) != j:
            raise CertError(f"step index mismatch at {j}")
        if _parse_bitstr(step["probe"], L, f"probe[{j}]") != trace[j]["probe"]:
            raise CertError(f"probe mismatch at step {j}")
        if _parse_bool(step["oracle_answer"], f"oracle_answer[{j}]") != trace[j]["oracle_answer"]:
            raise CertError(f"oracle_answer mismatch at step {j}")
        if _parse_bitstr(step["bit"], 1, f"bit[{j}]") != trace[j]["bit"]:
            raise CertError(f"bit mismatch at step {j}")

    if _parse_int(payload["claimed_co_onp_accepted_count"], "claimed_co_onp_accepted_count", 1, 1) != 1:
        raise CertError("co-ONP tester must accept exactly 1 canonical advice string")

    return {
        "bit_len": L,
        "feasible_count": len(feasible),
        "canonical_a_n": a_n,
        "co_onp_unique": True,
    }


def _verify_mode2(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 2: Lemma 2.8 Mahaney census checksum & Theorem 4.1 OUP bit-by-bit extraction."""
    _require_exact_keys(
        payload,
        {
            "input_len",
            "witness_len",
            "tally_bound_h",
            "tally_oracle_set",
            "claimed_census_cm",
            "claimed_paired_checksum",
            "accepted_pairs",
            "claimed_slice_nonempty",
            "claimed_extracted_witness",
            "claimed_bit_queries",
        },
        "mode2.payload",
    )
    n = _parse_int(payload["input_len"], "input_len", 2, 5)
    p = _parse_int(payload["witness_len"], "witness_len", 2, 6)
    h = _parse_int(payload["tally_bound_h"], "tally_bound_h", 1, 64)

    raw_tally = payload["tally_oracle_set"]
    if type(raw_tally) is not list or len(raw_tally) > h + 1:
        raise CertError("tally_oracle_set: invalid list")
    tally_set: Set[int] = set()
    for i, val in enumerate(raw_tally):
        k = _parse_int(val, f"tally_oracle_set[{i}]", 0, h)
        if k in tally_set:
            raise CertError(f"tally_oracle_set[{i}]: duplicate tally index {k}")
        tally_set.add(k)

    c_m = len(tally_set)
    if _parse_int(payload["claimed_census_cm"], "claimed_census_cm", 0, h + 1) != c_m:
        raise CertError(f"claimed_census_cm mismatch: expected {c_m}")
    paired = cantor_pair(n, c_m)
    if _parse_int(payload["claimed_paired_checksum"], "claimed_paired_checksum", 0) != paired:
        raise CertError(f"claimed_paired_checksum mismatch: expected {paired}")

    # Verify Cantor pairing injectivity across (n, i) for i=1..p
    seen_pairs: Set[int] = set()
    for i in range(1, p + 1):
        code = cantor_pair(n, i)
        if code in seen_pairs:
            raise CertError("Cantor pairing collision")
        seen_pairs.add(code)

    raw_acc = payload["accepted_pairs"]
    if type(raw_acc) is not list:
        raise CertError("accepted_pairs: expected list")
    acc_pairs: Set[Tuple[str, str]] = set()
    witnesses_seen: Set[str] = set()
    for idx, pair in enumerate(raw_acc):
        if type(pair) is not list or len(pair) != 2:
            raise CertError(f"accepted_pairs[{idx}]: expected [x, w]")
        x = _parse_bitstr(pair[0], n, f"accepted_pairs[{idx}][0]")
        w = _parse_bitstr(pair[1], p, f"accepted_pairs[{idx}][1]")
        if (x, w) in acc_pairs:
            raise CertError(f"accepted_pairs[{idx}]: duplicate pair")
        acc_pairs.add((x, w))
        witnesses_seen.add(w)

    # Oblivious unambiguity check: at most 1 distinct witness across ALL positive inputs of length n!
    if len(witnesses_seen) > 1:
        raise CertError(
            f"OUP violation: multiple distinct witnesses {sorted(witnesses_seen)} on inputs of length {n}"
        )

    nonempty = len(acc_pairs) > 0
    if _parse_bool(payload["claimed_slice_nonempty"], "claimed_slice_nonempty") != nonempty:
        raise CertError("claimed_slice_nonempty mismatch")

    extracted_w, bit_list = mahaney_extract_oup_witness(acc_pairs, p)
    expected_w = next(iter(witnesses_seen)) if nonempty else ("0" * p)
    if extracted_w != expected_w:
        raise CertError("Bit-by-bit witness extraction did not match oblivious witness")
    if _parse_bitstr(payload["claimed_extracted_witness"], p, "claimed_extracted_witness") != extracted_w:
        raise CertError(f"claimed_extracted_witness mismatch: expected {extracted_w!r}")

    claimed_bits = payload["claimed_bit_queries"]
    if type(claimed_bits) is not list or len(claimed_bits) != p or not all(type(b) is bool for b in claimed_bits):
        raise CertError(f"claimed_bit_queries: expected {p} strict booleans")
    if claimed_bits != bit_list:
        raise CertError("claimed_bit_queries mismatch")

    return {
        "census_cm": c_m,
        "slice_nonempty": nonempty,
        "extracted_witness": extracted_w,
        "accepted_inputs": len(acc_pairs),
    }


def _verify_mode3(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 3: Theorem 5.1 finite loose promise-oracle tower & round-termination generator."""
    _require_exact_keys(
        payload,
        {
            "depth",
            "inputs",
            "base_A0",
            "levels",
            "top_machine",
            "claimed_rounds",
            "claimed_every_round_adds_true_witness",
            "claimed_final_S",
            "claimed_decoder_matches",
            "claimed_true_outputs",
        },
        "mode3.payload",
    )
    depth = _parse_int(payload["depth"], "depth", 1, 3)
    raw_inputs = payload["inputs"]
    if type(raw_inputs) is not list or not (1 <= len(raw_inputs) <= 16):
        raise CertError("inputs: expected 1..16 input strings")
    inputs = [_parse_id_str(x, f"inputs[{i}]") for i, x in enumerate(raw_inputs)]
    if len(set(inputs)) != len(inputs):
        raise CertError("inputs: duplicate input")

    raw_A0 = payload["base_A0"]
    if type(raw_A0) is not dict or not raw_A0:
        raise CertError("base_A0: expected non-empty dict")
    base_A0: Dict[str, bool] = {}
    for k, v in raw_A0.items():
        base_A0[_parse_id_str(k, "base_A0.key")] = _parse_bool(v, f"base_A0[{k}]")

    raw_levels = payload["levels"]
    if type(raw_levels) is not list or len(raw_levels) != depth:
        raise CertError(f"levels: expected {depth} levels")

    levels: List[Dict[str, object]] = []
    prev_queries = set(base_A0.keys())
    # Track all consistent oracles at each level to verify loose-access unambiguity!
    consistent_oracles: List[List[Dict[str, bool]]] = [[dict(base_A0)]]

    for i, raw_lvl in enumerate(raw_levels):
        _require_exact_keys(
            raw_lvl,
            {"queries", "witnesses", "promise_yes", "promise_no", "true_witness", "verifier"},
            f"levels[{i}]",
        )
        for list_field in ("queries", "witnesses", "promise_yes", "promise_no"):
            if type(raw_lvl[list_field]) is not list:
                raise CertError(f"levels[{i}].{list_field}: expected list")
        qs = [_parse_id_str(q, f"levels[{i}].queries[{j}]") for j, q in enumerate(raw_lvl["queries"])]
        if not qs or len(set(qs)) != len(qs) or len(qs) > 8:
            raise CertError(f"levels[{i}].queries: expected 1..8 distinct queries")
        ws = [_parse_id_str(w, f"levels[{i}].witnesses[{j}]") for j, w in enumerate(raw_lvl["witnesses"])]
        if not ws or len(set(ws)) != len(ws) or len(ws) > 8:
            raise CertError(f"levels[{i}].witnesses: expected 1..8 distinct witnesses")
        pyes = set(_parse_id_str(q, f"levels[{i}].promise_yes") for q in raw_lvl["promise_yes"])
        pno = set(_parse_id_str(q, f"levels[{i}].promise_no") for q in raw_lvl["promise_no"])
        if pyes & pno:
            raise CertError(f"levels[{i}]: promise_yes and promise_no are not disjoint")
        if not (pyes <= set(qs) and pno <= set(qs)):
            raise CertError(f"levels[{i}]: promise sets must be subsets of queries")
        tw = _parse_id_str(raw_lvl["true_witness"], f"levels[{i}].true_witness")
        if tw not in ws:
            raise CertError(f"levels[{i}].true_witness must be in witnesses")

        raw_v = raw_lvl["verifier"]
        if type(raw_v) is not dict:
            raise CertError(f"levels[{i}].verifier: expected dict")
        expected_vkeys = {f"{q}|{w}" for q in qs for w in ws}
        if set(raw_v.keys()) != expected_vkeys:
            raise CertError(f"levels[{i}].verifier: keys must cover every q|w pair")
        vtab: Dict[str, Dict[str, object]] = {}
        for vk, entry in raw_v.items():
            _require_exact_keys(entry, {"query", "acc_if_0", "acc_if_1"}, f"levels[{i}].verifier[{vk}]")
            lq = entry["query"]
            if lq is not None:
                lqs = _parse_id_str(lq, f"levels[{i}].verifier[{vk}].query")
                if lqs not in prev_queries:
                    raise CertError(f"levels[{i}].verifier[{vk}]: lower query {lqs!r} not in level {i}")
            a0 = _parse_bool(entry["acc_if_0"], f"levels[{i}].verifier[{vk}].acc_if_0")
            a1 = _parse_bool(entry["acc_if_1"], f"levels[{i}].verifier[{vk}].acc_if_1")
            vtab[vk] = {"query": lq, "acc_if_0": a0, "acc_if_1": a1}

        # Verify loose-access prOUP semantics for ALL consistent oracles at level i:
        for O_prev in consistent_oracles[-1]:
            for q in pyes:
                acc_w = []
                for w in ws:
                    e = vtab[f"{q}|{w}"]
                    lq = e["query"]
                    res = bool(e["acc_if_0"]) if lq is None else (bool(e["acc_if_1"]) if O_prev[str(lq)] else bool(e["acc_if_0"]))
                    if res:
                        acc_w.append(w)
                if acc_w != [tw]:
                    raise CertError(
                        f"levels[{i}]: promised YES query {q!r} failed unique oblivious witness {tw!r} (got {acc_w})"
                    )
            for q in pno:
                for w in ws:
                    e = vtab[f"{q}|{w}"]
                    lq = e["query"]
                    res = bool(e["acc_if_0"]) if lq is None else (bool(e["acc_if_1"]) if O_prev[str(lq)] else bool(e["acc_if_0"]))
                    if res:
                        raise CertError(f"levels[{i}]: promised NO query {q!r} accepted witness {w!r}")

        # Build all consistent oracles at level i+1 (out-of-promise queries may take 0 or 1!)
        out_of_prom = [q for q in qs if q not in pyes and q not in pno]
        if len(out_of_prom) > 4:
            raise CertError(f"levels[{i}]: too many out-of-promise queries (>4)")
        next_oracles: List[Dict[str, bool]] = []
        for mask in range(1 << len(out_of_prom)):
            om: Dict[str, bool] = {}
            for q in pyes:
                om[q] = True
            for q in pno:
                om[q] = False
            for bit_i, q in enumerate(out_of_prom):
                om[q] = bool((mask >> bit_i) & 1)
            next_oracles.append(om)
        consistent_oracles.append(next_oracles)
        prev_queries = set(qs)
        levels.append(
            {
                "queries": qs,
                "witnesses": ws,
                "promise_yes": sorted(pyes),
                "promise_no": sorted(pno),
                "true_witness": tw,
                "verifier": vtab,
            }
        )

    raw_top = payload["top_machine"]
    if type(raw_top) is not dict or set(raw_top.keys()) != set(inputs):
        raise CertError("top_machine: must map every input")
    top_machine: Dict[str, Dict[str, object]] = {}
    for x in inputs:
        spec = _require_exact_keys(raw_top[x], {"query", "out_if_0", "out_if_1"}, f"top_machine[{x}]")
        qd = _parse_id_str(spec["query"], f"top_machine[{x}].query")
        if qd not in prev_queries:
            raise CertError(f"top_machine[{x}]: query {qd!r} not in top level")
        o0 = _parse_bool(spec["out_if_0"], f"top_machine[{x}].out_if_0")
        o1 = _parse_bool(spec["out_if_1"], f"top_machine[{x}].out_if_1")
        top_machine[x] = {"query": qd, "out_if_0": o0, "out_if_1": o1}

    # Verify top machine loose-access consistency: M^{O_d}(x) is identical for ALL consistent O_d!
    for x in inputs:
        spec = top_machine[x]
        qd = str(spec["query"])
        outs = {
            (bool(spec["out_if_1"]) if Od[qd] else bool(spec["out_if_0"]))
            for Od in consistent_oracles[-1]
        }
        if len(outs) != 1:
            raise CertError(f"top_machine[{x}]: output depends on out-of-promise answer to {qd!r}")

    sim = simulate_loose_promise_tower(inputs, depth, base_A0, levels, top_machine)
    rounds = int(sim["rounds"])  # type: ignore[arg-type]
    if rounds > depth:
        raise CertError(f"Generator exceeded Theorem 5.1 round bound d={depth} (took {rounds})")
    trace: List[Dict[str, object]] = sim["trace"]  # type: ignore[assignment]
    every_true = all(bool(t["added_missing_true_witness"]) for t in trace)
    if not every_true:
        raise CertError("Theorem 5.1 invariant violated: some round failed to add a missing true witness")
    if not bool(sim["decoder_matches_exact"]):
        raise CertError("Final decoder D(x, S) failed to match M^{A_d}(x)")

    if _parse_int(payload["claimed_rounds"], "claimed_rounds", 0, depth) != rounds:
        raise CertError(f"claimed_rounds mismatch: expected {rounds}")
    if _parse_bool(payload["claimed_every_round_adds_true_witness"], "claimed_every_round_adds_true_witness") != every_true:
        raise CertError("claimed_every_round_adds_true_witness mismatch")
    raw_final_S = payload["claimed_final_S"]
    if type(raw_final_S) is not list or len(raw_final_S) != depth:
        raise CertError(f"claimed_final_S: expected list of {depth} witness lists")
    parsed_final_S: List[List[str]] = []
    for li, bucket in enumerate(raw_final_S):
        if type(bucket) is not list:
            raise CertError(f"claimed_final_S[{li}]: expected list")
        parsed_final_S.append([_parse_id_str(w, f"claimed_final_S[{li}][{wi}]") for wi, w in enumerate(bucket)])
    if parsed_final_S != sim["final_S"]:
        raise CertError(f"claimed_final_S mismatch: expected {sim['final_S']}")
    if _parse_bool(payload["claimed_decoder_matches"], "claimed_decoder_matches") is not True:
        raise CertError("claimed_decoder_matches must be True")
    raw_true_out = payload["claimed_true_outputs"]
    if type(raw_true_out) is not dict or set(raw_true_out.keys()) != set(inputs):
        raise CertError("claimed_true_outputs: expected dict covering all inputs")
    parsed_true_out = {x: _parse_bool(raw_true_out[x], f"claimed_true_outputs[{x}]") for x in inputs}
    if parsed_true_out != sim["true_outputs"]:
        raise CertError("claimed_true_outputs mismatch")

    return {
        "depth": depth,
        "rounds": rounds,
        "final_S_sizes": [len(s) for s in sim["final_S"]],  # type: ignore[union-attr]
        "decoder_matches": True,
    }


def _verify_mode4(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 4: Section 6 theorems (Thm. 6.2 dot-op collapse, Lem. 6.4/Thm. 6.5 tagging, Prop. 6.6 SOUP)."""
    if type(payload) is not dict or "submode" not in payload:
        raise CertError("mode4.payload: missing submode")
    submode = _parse_id_str(payload["submode"], "submode")

    if submode == "dot_op_collapse":
        _require_exact_keys(
            payload,
            {
                "submode",
                "input_len",
                "outer_w_len",
                "inner_v_len",
                "outer_witness_w_n",
                "inner_witness_v_N",
                "language_L",
                "inner_verifier_Rbar",
                "claimed_probe_refutes_0p",
                "claimed_probe_refutes_1p",
                "claimed_unique_pair_ok",
            },
            "mode4.dot_op_collapse",
        )
        n = _parse_int(payload["input_len"], "input_len", 1, 3)
        p = _parse_int(payload["outer_w_len"], "outer_w_len", 1, 3)
        q = _parse_int(payload["inner_v_len"], "inner_v_len", 1, 3)
        w_n = _parse_bitstr(payload["outer_witness_w_n"], p, "outer_witness_w_n")
        v_N = _parse_bitstr(payload["inner_witness_v_N"], q, "inner_witness_v_N")

        xs = all_bitstrings(n)
        ws = all_bitstrings(p)
        vs = all_bitstrings(q)

        raw_L = payload["language_L"]
        if type(raw_L) is not dict or set(raw_L.keys()) != set(xs):
            raise CertError("language_L must map every x in {0,1}^n")
        L_map = {x: _parse_bool(raw_L[x], f"language_L[{x}]") for x in xs}

        raw_V = payload["inner_verifier_Rbar"]
        expected_keys = {f"{x}|{w}|{v}" for x in xs for w in ws for v in vs}
        if type(raw_V) is not dict or set(raw_V.keys()) != expected_keys:
            raise CertError("inner_verifier_Rbar must map every x|w|v triple")
        V_map = {k: _parse_bool(raw_V[k], f"inner_verifier_Rbar[{k}]") for k in expected_keys}

        # Verify inner verifier V is a valid OUP verifier for R-bar with oblivious witness v_N:
        # (x, w) in R iff (L[x] and w == w_n); so (x, w) in R-bar iff not (L[x] and w == w_n)!
        for x in xs:
            for w in ws:
                in_R = L_map[x] and (w == w_n)
                acc_vs = [v for v in vs if V_map[f"{x}|{w}|{v}"]]
                if in_R:
                    if acc_vs:
                        raise CertError(f"({x},{w}) in R must reject all v, got {acc_vs}")
                else:
                    if acc_vs != [v_N]:
                        raise CertError(f"({x},{w}) in R-bar must uniquely accept {v_N}, got {acc_vs}")

        z_n = "0" * n
        p0 = "0" * p
        p1 = "1" * p
        probe_0 = any(V_map[f"{z_n}|{p0}|{v}"] for v in vs)
        probe_1 = any(V_map[f"{z_n}|{p1}|{v}"] for v in vs)
        if not (probe_0 or probe_1):
            raise CertError("Theorem 6.2 probe failed: neither (0^n, 0^p) nor (0^n, 1^p) refuted R")

        # Verify Theorem 6.2 combined OUP verifier Acc(x, (w, v)) := (V(0^n,0^p,v) or V(0^n,1^p,v)) and not V(x,w,v)
        for x in xs:
            acc_pairs = [
                (w, v)
                for w in ws
                for v in vs
                if (V_map[f"{z_n}|{p0}|{v}"] or V_map[f"{z_n}|{p1}|{v}"]) and (not V_map[f"{x}|{w}|{v}"])
            ]
            if L_map[x]:
                if acc_pairs != [(w_n, v_N)]:
                    raise CertError(f"Combined OUP verifier failed on x={x}: got {acc_pairs}")
            else:
                if acc_pairs:
                    raise CertError(f"Combined OUP verifier accepted on x={x} not in L: {acc_pairs}")

        if _parse_bool(payload["claimed_probe_refutes_0p"], "claimed_probe_refutes_0p") != probe_0:
            raise CertError("claimed_probe_refutes_0p mismatch")
        if _parse_bool(payload["claimed_probe_refutes_1p"], "claimed_probe_refutes_1p") != probe_1:
            raise CertError("claimed_probe_refutes_1p mismatch")
        if _parse_bool(payload["claimed_unique_pair_ok"], "claimed_unique_pair_ok") is not True:
            raise CertError("claimed_unique_pair_ok must be True")

        return {"submode": submode, "unique_pair": f"({w_n}, {v_N})", "probe_ok": True}

    if submode == "single_loose_query":
        _require_exact_keys(
            payload,
            {
                "submode",
                "inputs",
                "witnesses",
                "true_witness",
                "language_L",
                "promise_yes",
                "promise_no",
                "out_of_promise",
                "query_map",
                "verifier_if_0",
                "verifier_if_1",
                "claimed_mattering_set_size",
                "claimed_tagged_A_size",
            },
            "mode4.single_loose_query",
        )
        for list_field in ("inputs", "witnesses", "promise_yes", "promise_no", "out_of_promise"):
            if type(payload[list_field]) is not list:
                raise CertError(f"mode4.single_loose_query.{list_field}: expected list")
        inputs = [_parse_id_str(x, "inputs") for x in payload["inputs"]]
        ws = [_parse_id_str(w, "witnesses") for w in payload["witnesses"]]
        if not inputs or not ws or len(set(inputs)) != len(inputs) or len(set(ws)) != len(ws):
            raise CertError("inputs and witnesses must be non-empty distinct lists")
        tw = _parse_id_str(payload["true_witness"], "true_witness")
        if tw not in ws:
            raise CertError("true_witness not in witnesses")
        raw_L = payload["language_L"]
        if type(raw_L) is not dict or set(raw_L.keys()) != set(inputs):
            raise CertError("language_L: expected dict mapping all inputs")
        L_map = {x: _parse_bool(raw_L[x], f"L[{x}]") for x in inputs}

        pyes = set(_parse_id_str(q, "pyes") for q in payload["promise_yes"])
        pno = set(_parse_id_str(q, "pno") for q in payload["promise_no"])
        pout = set(_parse_id_str(q, "pout") for q in payload["out_of_promise"])
        if (pyes & pno) or (pyes & pout) or (pno & pout):
            raise CertError("promise_yes, promise_no, out_of_promise must be pairwise disjoint")
        all_qs = pyes | pno | pout
        if not all_qs:
            raise CertError("empty query universe")

        expected_pairs = {f"{x}|{w}" for x in inputs for w in ws}
        qmap = payload["query_map"]
        v0 = payload["verifier_if_0"]
        v1 = payload["verifier_if_1"]
        if (
            type(qmap) is not dict
            or type(v0) is not dict
            or type(v1) is not dict
            or set(qmap.keys()) != expected_pairs
            or set(v0.keys()) != expected_pairs
            or set(v1.keys()) != expected_pairs
        ):
            raise CertError("query_map, verifier_if_0, verifier_if_1 must map all x|w pairs")

        for k in expected_pairs:
            if _parse_id_str(qmap[k], f"qmap[{k}]") not in all_qs:
                raise CertError(f"qmap[{k}] outside query universe")
            _parse_bool(v0[k], f"v0[{k}]")
            _parse_bool(v1[k], f"v1[{k}]")

        # Check loose OUP correctness across ALL consistent oracles
        pout_list = sorted(pout)
        if len(pout_list) > 5:
            raise CertError("too many out_of_promise queries (>5)")
        for mask in range(1 << len(pout_list)):
            oracle = {q: True for q in pyes}
            oracle.update({q: False for q in pno})
            for bit_i, q in enumerate(pout_list):
                oracle[q] = bool((mask >> bit_i) & 1)
            for x in inputs:
                acc_ws = [
                    w
                    for w in ws
                    if (v1[f"{x}|{w}"] if oracle[qmap[f"{x}|{w}"]] else v0[f"{x}|{w}"])
                ]
                if L_map[x]:
                    if acc_ws != [tw]:
                        raise CertError(f"Loose OUP failed on x={x} (got {acc_ws})")
                else:
                    if acc_ws:
                        raise CertError(f"Loose OUP accepted on x={x} not in L (got {acc_ws})")

        # Lemma 6.4: compute T = {(x,w) : v0 != v1} and verify every q(x,w) for (x,w) in T lies in promise!
        T_set = {k for k in expected_pairs if v0[k] != v1[k]}
        for k in T_set:
            if qmap[k] in pout:
                raise CertError(f"Lemma 6.4 violated: mattering pair {k} queries out-of-promise {qmap[k]}")

        # Theorem 6.5: tagged language A = {k in T : q(k) in pyes} reproduces L identically!
        A_set = {k for k in T_set if qmap[k] in pyes}
        for x in inputs:
            acc_ws = []
            for w in ws:
                k = f"{x}|{w}"
                val = v0[k] if k not in T_set else (v1[k] if k in A_set else v0[k])
                if val:
                    acc_ws.append(w)
            if L_map[x] and acc_ws != [tw]:
                raise CertError(f"Tagged language A simulation failed on x={x}")
            if (not L_map[x]) and acc_ws:
                raise CertError(f"Tagged language A simulation accepted on x={x} not in L")

        if _parse_int(payload["claimed_mattering_set_size"], "claimed_mattering_set_size", 0) != len(T_set):
            raise CertError(f"claimed_mattering_set_size mismatch: expected {len(T_set)}")
        if _parse_int(payload["claimed_tagged_A_size"], "claimed_tagged_A_size", 0) != len(A_set):
            raise CertError(f"claimed_tagged_A_size mismatch: expected {len(A_set)}")

        return {"submode": submode, "mattering_size": len(T_set), "tagged_A_size": len(A_set)}

    if submode == "soup_intersection":
        _require_exact_keys(
            payload,
            {
                "submode",
                "input_len",
                "witness_len",
                "language_L",
                "witness_Y",
                "witness_Z",
                "verifier_Y",
                "verifier_Z",
                "claimed_soup_bit",
                "claimed_soup_witness",
            },
            "mode4.soup_intersection",
        )
        n = _parse_int(payload["input_len"], "input_len", 1, 4)
        p = _parse_int(payload["witness_len"], "witness_len", 1, 4)
        xs = all_bitstrings(n)
        ws = all_bitstrings(p)
        wY = _parse_bitstr(payload["witness_Y"], p, "witness_Y")
        wZ = _parse_bitstr(payload["witness_Z"], p, "witness_Z")

        raw_L = payload["language_L"]
        if type(raw_L) is not dict or set(raw_L.keys()) != set(xs):
            raise CertError("language_L key mismatch")
        L_map = {x: _parse_bool(raw_L[x], f"L[{x}]") for x in xs}

        expected_pairs = {f"{x}|{w}" for x in xs for w in ws}
        raw_Y = payload["verifier_Y"]
        raw_Z = payload["verifier_Z"]
        if type(raw_Y) is not dict or set(raw_Y.keys()) != expected_pairs:
            raise CertError("verifier_Y key mismatch")
        if type(raw_Z) is not dict or set(raw_Z.keys()) != expected_pairs:
            raise CertError("verifier_Z key mismatch")
        Y_map = {k: _parse_bool(raw_Y[k], f"Y[{k}]") for k in expected_pairs}
        Z_map = {k: _parse_bool(raw_Z[k], f"Z[{k}]") for k in expected_pairs}

        # Verify Y is OUP for L with witness wY, and Z is OUP for not-L with witness wZ
        for x in xs:
            accY = [w for w in ws if Y_map[f"{x}|{w}"]]
            accZ = [w for w in ws if Z_map[f"{x}|{w}"]]
            if L_map[x]:
                if accY != [wY] or accZ:
                    raise CertError(f"OUP/co-OUP violation on x={x} in L")
            else:
                if accY or accZ != [wZ]:
                    raise CertError(f"OUP/co-OUP violation on x={x} not in L")

        # Proposition 6.6 combined witness check on 0^n:
        z_n = "0" * n
        valid_pairs = [
            (b, w)
            for b in (0, 1)
            for w in ws
            if (b == 1 and Y_map[f"{z_n}|{w}"]) or (b == 0 and Z_map[f"{z_n}|{w}"])
        ]
        if len(valid_pairs) != 1:
            raise CertError(f"Proposition 6.6 probe failed uniqueness: {valid_pairs}")
        b_star, w_star = valid_pairs[0]

        # Verify (b_star, w_star) decides every x in {0,1}^n identically to L[x]
        for x in xs:
            dec = Y_map[f"{x}|{w_star}"] if b_star == 1 else (not Z_map[f"{x}|{w_star}"])
            if dec != L_map[x]:
                raise CertError(f"SOUP combined witness failed to decide x={x}")

        if _parse_int(payload["claimed_soup_bit"], "claimed_soup_bit", 0, 1) != b_star:
            raise CertError(f"claimed_soup_bit mismatch: expected {b_star}")
        if _parse_bitstr(payload["claimed_soup_witness"], p, "claimed_soup_witness") != w_star:
            raise CertError(f"claimed_soup_witness mismatch: expected {w_star!r}")

        return {"submode": submode, "soup_pair": f"({b_star}, {w_star})"}

    raise CertError(f"unknown mode4 submode {submode!r}")


def verify_certificate(cert: Any) -> Tuple[bool, str, Dict[str, Any]]:
    """Verify an OUH-CERT-1.0 certificate payload with zero floating-point arithmetic."""
    try:
        _assert_strict_json_types(cert)
        _require_exact_keys(
            cert,
            {"schema_version", "cert_id", "mode", "reference", "payload"},
            "certificate",
        )
        if cert["schema_version"] != SCHEMA_VERSION:
            raise CertError(
                f"schema_version mismatch: expected {SCHEMA_VERSION!r}, got {cert['schema_version']!r}"
            )
        cert_id = _parse_id_str(cert["cert_id"], "cert_id")
        mode = _parse_id_str(cert["mode"], "mode")
        if mode not in VALID_MODES:
            raise CertError(f"unknown mode {mode!r}")
        _parse_id_str(cert["reference"], "reference")
        payload = cert["payload"]
        if type(payload) is not dict:
            raise CertError("payload must be a dict")

        if mode == "canonical_advice_ogtd_cert":
            summary = _verify_mode1(payload)
        elif mode == "mahaney_census_ouh_cert":
            summary = _verify_mode2(payload)
        elif mode == "loose_promise_tower_cert":
            summary = _verify_mode3(payload)
        else:
            summary = _verify_mode4(payload)

        summary["cert_id"] = cert_id
        summary["mode"] = mode
        return True, "OK", summary
    except CertError as exc:
        return False, str(exc), {}
