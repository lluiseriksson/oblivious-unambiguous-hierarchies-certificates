"""Exact finite-combinatorial helpers for input-oblivious unambiguous hierarchies (OUH-CERT-1.0).

Strictly zero floating-point operations (uses exact int, bool, str, and fractions.Fraction only).
Author: Lluis Eriksson
License: MIT
"""

from __future__ import annotations

from typing import Dict, List, Optional, Sequence, Set, Tuple


def is_bitstring(s: str, length: Optional[int] = None) -> bool:
    if type(s) is not str:
        return False
    if length is not None and len(s) != length:
        return False
    return all(ch in ("0", "1") for ch in s)


def all_bitstrings(length: int) -> List[str]:
    return [format(i, f"0{length}b") for i in range(1 << length)]


def cantor_pair(a: int, b: int) -> int:
    if a < 0 or b < 0:
        raise ValueError("Cantor pairing requires non-negative integers")
    s = a + b
    return (s * (s + 1)) // 2 + b


def prefix_search_lex_max(feasible: Set[str], bit_len: int) -> Tuple[str, List[Dict[str, object]]]:
    """Execute Lemma 3.1's FP^ONP bit-by-bit prefix search for lex-max feasible string a_n."""
    if not feasible:
        raise ValueError("Feasible set must be non-empty")
    prefix = ""
    trace: List[Dict[str, object]] = []
    for j in range(bit_len):
        probe = prefix + "1" + ("0" * (bit_len - j - 1))
        ans = any(a >= probe for a in feasible)
        bit = "1" if ans else "0"
        trace.append({"step": j, "probe": probe, "oracle_answer": ans, "bit": bit})
        prefix += bit
    return prefix, trace


def co_onp_tester_accepted(feasible: Set[str], bit_len: int) -> List[str]:
    """Compute Acc_T = {a in {0,1}^L : R(a) and forall b >_lex a, not R(b)}."""
    acc: List[str] = []
    for a in all_bitstrings(bit_len):
        if a in feasible and not any(b > a for b in feasible):
            acc.append(a)
    return acc


def mahaney_extract_oup_witness(
    accepted_pairs: Set[Tuple[str, str]], witness_len: int
) -> Tuple[str, List[bool]]:
    """Execute Theorem 4.1 bit-by-bit tally extraction W(1^{pi(n,i)}) for i=0..p-1."""
    bits: List[bool] = []
    for i in range(witness_len):
        b = any(w[i] == "1" for (_, w) in accepted_pairs)
        bits.append(b)
    return "".join("1" if b else "0" for b in bits), bits


def simulate_loose_promise_tower(
    inputs: Sequence[str],
    depth: int,
    base_A0: Dict[str, bool],
    levels: Sequence[Dict[str, object]],
    top_machine: Dict[str, Dict[str, object]],
) -> Dict[str, object]:
    """Exact finite simulation of Hirsch Theorem 5.1 FP^NP generator for OUH^•.

    Model per level i in 1..depth:
      - `queries`: list of query strings at level i (all same length m_i for simplicity or tagged)
      - `witnesses`: list of candidate witness strings at level i
      - `promise_yes`: list of promised YES queries
      - `promise_no`: list of promised NO queries
      - `true_witness`: single oblivious unambiguous witness w_i on promised YES queries
      - `verifier`: dict mapping (q, w) -> {"query": lower_q_or_None, "acc_if_0": bool, "acc_if_1": bool}
        (each V_i makes 0 or 1 deterministic query to level i-1).
    Top deterministic machine M on input x:
      - `top_machine[x]` = {"query": level_d_query, "out_if_0": bool, "out_if_1": bool}.
    """
    # 1. Build canonical consistent languages A_0, A_1, ..., A_d
    A: List[Dict[str, bool]] = [dict(base_A0)]
    for lvl in levels:
        prev_A = A[-1]
        cur_A: Dict[str, bool] = {}
        queries: List[str] = lvl["queries"]  # type: ignore[assignment]
        witnesses: List[str] = lvl["witnesses"]  # type: ignore[assignment]
        vtab: Dict[str, Dict[str, object]] = lvl["verifier"]  # type: ignore[assignment]
        for q in queries:
            found = False
            for w in witnesses:
                entry = vtab[f"{q}|{w}"]
                lq = entry["query"]
                if lq is None:
                    val = bool(entry["acc_if_0"])
                else:
                    ans = prev_A[str(lq)]
                    val = bool(entry["acc_if_1"]) if ans else bool(entry["acc_if_0"])
                if val:
                    found = True
                    break
            cur_A[q] = found
        A.append(cur_A)

    def eval_top(oracle_d: Dict[str, bool], x: str) -> bool:
        spec = top_machine[x]
        q = str(spec["query"])
        return bool(spec["out_if_1"]) if oracle_d[q] else bool(spec["out_if_0"])

    # Compute exact certified-answer sets at each level wrt candidate witness sets S[1..d]
    # cert_pos[i][q] = list of witnesses w that have a certified accepting run of V_i(q, w)
    # cert_neg[i][q] = True iff every s in S[i] has a certified rejecting run of V_i(q, s)
    def compute_certified(S: List[Set[str]]) -> Tuple[List[Dict[str, List[str]]], List[Dict[str, bool]]]:
        # Level 0: only exact base_A0(q) is certified
        c_pos: List[Dict[str, List[str]]] = [{q: (["eps"] if v else []) for q, v in base_A0.items()}]
        c_neg: List[Dict[str, bool]] = [{q: (not v) for q, v in base_A0.items()}]

        for idx, lvl in enumerate(levels):
            prev_pos = c_pos[idx]
            prev_neg = c_neg[idx]
            queries: List[str] = lvl["queries"]  # type: ignore[assignment]
            witnesses: List[str] = lvl["witnesses"]  # type: ignore[assignment]
            vtab: Dict[str, Dict[str, object]] = lvl["verifier"]  # type: ignore[assignment]
            Si = S[idx]

            cur_pos: Dict[str, List[str]] = {}
            cur_neg: Dict[str, bool] = {}

            for q in queries:
                pos_ws: List[str] = []
                for w in witnesses:
                    entry = vtab[f"{q}|{w}"]
                    lq = entry["query"]
                    can_acc = False
                    if lq is None:
                        can_acc = bool(entry["acc_if_0"])
                    else:
                        lqs = str(lq)
                        if prev_pos[lqs] and bool(entry["acc_if_1"]):
                            can_acc = True
                        if prev_neg[lqs] and bool(entry["acc_if_0"]):
                            can_acc = True
                    if can_acc:
                        pos_ws.append(w)
                cur_pos[q] = pos_ws

                # Certified negative iff every s in Si has a certified rejecting run
                all_rej = True
                for s in Si:
                    entry = vtab[f"{q}|{s}"]
                    lq = entry["query"]
                    can_rej = False
                    if lq is None:
                        can_rej = not bool(entry["acc_if_0"])
                    else:
                        lqs = str(lq)
                        if prev_pos[lqs] and (not bool(entry["acc_if_1"])):
                            can_rej = True
                        if prev_neg[lqs] and (not bool(entry["acc_if_0"])):
                            can_rej = True
                    if not can_rej:
                        all_rej = False
                        break
                cur_neg[q] = all_rej

            c_pos.append(cur_pos)
            c_neg.append(cur_neg)
        return c_pos, c_neg

    def build_B(S: List[Set[str]]) -> List[Dict[str, bool]]:
        B: List[Dict[str, bool]] = [dict(base_A0)]
        for idx, lvl in enumerate(levels):
            prev_B = B[-1]
            cur_B: Dict[str, bool] = {}
            queries: List[str] = lvl["queries"]  # type: ignore[assignment]
            vtab: Dict[str, Dict[str, object]] = lvl["verifier"]  # type: ignore[assignment]
            for q in queries:
                found = False
                for s in S[idx]:
                    entry = vtab[f"{q}|{s}"]
                    lq = entry["query"]
                    if lq is None:
                        val = bool(entry["acc_if_0"])
                    else:
                        val = bool(entry["acc_if_1"]) if prev_B[str(lq)] else bool(entry["acc_if_0"])
                    if val:
                        found = True
                        break
                cur_B[q] = found
            B.append(cur_B)
        return B

    # Run Hirsch's Theorem 5.1 generator rounds from S = [empty, ..., empty]
    S: List[Set[str]] = [set() for _ in range(depth)]
    rounds_trace: List[Dict[str, object]] = []
    max_rounds = depth + 2

    for r in range(max_rounds):
        c_pos, c_neg = compute_certified(S)
        # Find an input x where M has two certified runs with different outputs
        disagree_x: Optional[str] = None
        for x in inputs:
            spec = top_machine[x]
            qd = str(spec["query"])
            outs: Set[bool] = set()
            if c_pos[depth][qd]:
                outs.add(bool(spec["out_if_1"]))
            if c_neg[depth][qd]:
                outs.add(bool(spec["out_if_0"]))
            if len(outs) == 2:
                disagree_x = x
                break
        if disagree_x is None:
            break

        # Recursively inspect negative answers in certified runs starting from disagree_x
        scheduled: List[Set[str]] = [set() for _ in range(depth)]
        visited: Set[Tuple[int, str, bool]] = set()

        def inspect_cert_ans(lvl_idx: int, q: str, ans: bool) -> None:
            key = (lvl_idx, q, ans)
            if key in visited or lvl_idx == 0:
                return
            visited.add(key)
            lvl = levels[lvl_idx - 1]
            vtab: Dict[str, Dict[str, object]] = lvl["verifier"]  # type: ignore[assignment]
            if ans:
                # Pick first certified accepting witness (prefer true witness if certified, else deterministic first)
                ws = c_pos[lvl_idx][q]
                if not ws:
                    return
                w = ws[0]
                entry = vtab[f"{q}|{w}"]
                lq = entry["query"]
                if lq is not None:
                    lqs = str(lq)
                    if c_pos[lvl_idx - 1][lqs] and bool(entry["acc_if_1"]):
                        inspect_cert_ans(lvl_idx - 1, lqs, True)
                    if c_neg[lvl_idx - 1][lqs] and bool(entry["acc_if_0"]):
                        inspect_cert_ans(lvl_idx - 1, lqs, False)
            else:
                # Negative answer at level lvl_idx: inspect all rejecting runs for s in S[lvl_idx-1]
                for s in sorted(S[lvl_idx - 1]):
                    entry = vtab[f"{q}|{s}"]
                    lq = entry["query"]
                    if lq is not None:
                        lqs = str(lq)
                        if c_pos[lvl_idx - 1][lqs] and (not bool(entry["acc_if_1"])):
                            inspect_cert_ans(lvl_idx - 1, lqs, True)
                        if c_neg[lvl_idx - 1][lqs] and (not bool(entry["acc_if_0"])):
                            inspect_cert_ans(lvl_idx - 1, lqs, False)
                # Ask NP oracle if q has a certified positive answer; schedule its witness and inspect it
                ws = c_pos[lvl_idx][q]
                if ws:
                    w_add = ws[0]
                    scheduled[lvl_idx - 1].add(w_add)
                    inspect_cert_ans(lvl_idx, q, True)

        qd = str(top_machine[disagree_x]["query"])
        inspect_cert_ans(depth, qd, True)
        inspect_cert_ans(depth, qd, False)

        # Check whether a previously missing true witness was added this round
        added_true = False
        for idx in range(depth):
            tw = str(levels[idx]["true_witness"])
            if tw in scheduled[idx] and tw not in S[idx]:
                added_true = True
            S[idx] |= scheduled[idx]
        rounds_trace.append(
            {
                "round": r + 1,
                "disagree_input": disagree_x,
                "scheduled": [sorted(sc) for sc in scheduled],
                "added_missing_true_witness": added_true,
            }
        )

    B_final = build_B(S)
    decoder_matches = all(eval_top(B_final[depth], x) == eval_top(A[depth], x) for x in inputs)
    return {
        "rounds": len(rounds_trace),
        "trace": rounds_trace,
        "final_S": [sorted(s) for s in S],
        "decoder_matches_exact": decoder_matches,
        "true_outputs": {x: eval_top(A[depth], x) for x in inputs},
    }
