"""Live 65-attack adversarial red-team test suite for OUH-CERT-1.0.

Tests 13 global schema/typing/depth/control-char attacks + 12 Mode 1 + 12 Mode 2 + 15 Mode 3 + 13 Mode 4 attacks.
Author: Lluis Eriksson
License: MIT
"""

from __future__ import annotations

import copy
import json
from pathlib import Path
import sys
from typing import Any, Callable, List, Tuple

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.ouh_certifier import verify_certificate


def _load(name: str) -> dict[str, Any]:
    return json.loads((ROOT / "certificates" / f"{name}.json").read_text(encoding="utf-8"))


def _mutate(cert: dict[str, Any], fn: Callable[[dict[str, Any]], None]) -> dict[str, Any]:
    c = copy.deepcopy(cert)
    fn(c)
    return c


def build_attacks() -> List[Tuple[str, str, Any]]:
    m1 = _load("m1_canonical_advice_len4_sparse")
    m2 = _load("m2_mahaney_ouh_nonempty_n3_p4")
    m3 = _load("m3_loose_tower_depth2_spurious_oop")
    m4_dot = _load("m4_dot_op_collapse_probe_1p")
    m4_tag = _load("m4_single_loose_query_tagging")
    m4_soup = _load("m4_soup_equals_oup_inter_co_oup")

    attacks: List[Tuple[str, str, Any]] = []

    # --- 12 Global Schema / Type / Depth / Control-Char Attacks ---
    attacks.append(("global", "g01_wrong_schema_version", _mutate(m1, lambda c: c.__setitem__("schema_version", "OUH-CERT-2.0"))))
    attacks.append(("global", "g02_unknown_mode", _mutate(m1, lambda c: c.__setitem__("mode", "bogus_mode"))))
    attacks.append(("global", "g03_extra_top_key", _mutate(m1, lambda c: c.__setitem__("extra", 1))))
    attacks.append(("global", "g04_missing_payload_key", _mutate(m1, lambda c: c["payload"].pop("bit_len"))))
    attacks.append(("global", "g05_raw_float_injected", _mutate(m1, lambda c: c["payload"].__setitem__("bit_len", 4.0))))
    attacks.append(("global", "g06_bool_as_int_bit_len", _mutate(m1, lambda c: c["payload"].__setitem__("bit_len", True))))
    attacks.append(("global", "g07_int_as_bool_oracle_ans", _mutate(m1, lambda c: c["payload"]["claimed_prefix_queries"][0].__setitem__("oracle_answer", 1))))
    attacks.append(("global", "g08_newline_in_cert_id", _mutate(m1, lambda c: c.__setitem__("cert_id", "bad\nid"))))
    attacks.append(("global", "g09_excess_id_len", _mutate(m1, lambda c: c.__setitem__("cert_id", "a" * 200))))
    attacks.append(("global", "g10_excess_int_bits", _mutate(m2, lambda c: c["payload"].__setitem__("claimed_paired_checksum", 1 << 2100))))
    attacks.append(("global", "g11_int_as_bool_bit_queries", _mutate(m2, lambda c: c["payload"]["claimed_bit_queries"].__setitem__(0, 1))))

    def _deep_nest(c: dict[str, Any]) -> None:
        node: Any = "leaf"
        for _ in range(40):
            node = [node]
        c["payload"]["feasible_encodings"] = node

    attacks.append(("global", "g12_excess_json_depth", _mutate(m1, _deep_nest)))
    attacks.append(("global", "g13_nul_control_char_in_id", _mutate(m1, lambda c: c.__setitem__("cert_id", "bad\x00id"))))

    # --- 12 Mode 1 Domain Attacks ---
    attacks.append(("mode1", "m1_01_empty_feasible_set", _mutate(m1, lambda c: c["payload"].__setitem__("feasible_encodings", []))))
    attacks.append(("mode1", "m1_02_duplicate_feasible_str", _mutate(m1, lambda c: c["payload"]["feasible_encodings"].append("0010"))))
    attacks.append(("mode1", "m1_03_wrong_bitstr_len", _mutate(m1, lambda c: c["payload"]["feasible_encodings"].__setitem__(0, "001"))))
    attacks.append(("mode1", "m1_04_non_binary_char", _mutate(m1, lambda c: c["payload"]["feasible_encodings"].__setitem__(0, "0012"))))
    attacks.append(("mode1", "m1_05_non_max_claimed_a_n", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_canonical_a_n", "1001"))))
    attacks.append(("mode1", "m1_06_infeasible_claimed_a_n", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_canonical_a_n", "1111"))))
    attacks.append(("mode1", "m1_07_wrong_prefix_probe", _mutate(m1, lambda c: c["payload"]["claimed_prefix_queries"][1].__setitem__("probe", "1111"))))
    attacks.append(("mode1", "m1_08_wrong_prefix_oracle_ans", _mutate(m1, lambda c: c["payload"]["claimed_prefix_queries"][0].__setitem__("oracle_answer", False))))
    attacks.append(("mode1", "m1_09_wrong_prefix_bit", _mutate(m1, lambda c: c["payload"]["claimed_prefix_queries"][0].__setitem__("bit", "0"))))
    attacks.append(("mode1", "m1_10_truncated_prefix_trace", _mutate(m1, lambda c: c["payload"]["claimed_prefix_queries"].pop())))
    attacks.append(("mode1", "m1_11_wrong_step_index", _mutate(m1, lambda c: c["payload"]["claimed_prefix_queries"][0].__setitem__("step", 1))))
    attacks.append(("mode1", "m1_12_co_onp_count_not_one", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_co_onp_accepted_count", 2))))

    # --- 12 Mode 2 Domain Attacks ---
    attacks.append(("mode2", "m2_01_duplicate_tally_idx", _mutate(m2, lambda c: c["payload"]["tally_oracle_set"].append(0))))
    attacks.append(("mode2", "m2_02_tally_idx_above_h", _mutate(m2, lambda c: c["payload"]["tally_oracle_set"].__setitem__(0, 13))))
    attacks.append(("mode2", "m2_03_wrong_census_cm", _mutate(m2, lambda c: c["payload"].__setitem__("claimed_census_cm", 4))))
    attacks.append(("mode2", "m2_04_wrong_paired_checksum", _mutate(m2, lambda c: c["payload"].__setitem__("claimed_paired_checksum", 1))))
    attacks.append(("mode2", "m2_05_non_oblivious_two_witnesses", _mutate(m2, lambda c: c["payload"]["accepted_pairs"].append(["100", "0100"]))))
    attacks.append(("mode2", "m2_06_duplicate_accepted_pair", _mutate(m2, lambda c: c["payload"]["accepted_pairs"].append(["001", "1011"]))))
    attacks.append(("mode2", "m2_07_wrong_slice_nonempty", _mutate(m2, lambda c: c["payload"].__setitem__("claimed_slice_nonempty", False))))
    attacks.append(("mode2", "m2_08_wrong_extracted_witness", _mutate(m2, lambda c: c["payload"].__setitem__("claimed_extracted_witness", "0000"))))
    attacks.append(("mode2", "m2_09_wrong_bit_queries", _mutate(m2, lambda c: c["payload"]["claimed_bit_queries"].__setitem__(0, False))))
    attacks.append(("mode2", "m2_10_bad_input_bitstr_len", _mutate(m2, lambda c: c["payload"]["accepted_pairs"][0].__setitem__(0, "01"))))
    attacks.append(("mode2", "m2_11_bad_witness_bitstr_len", _mutate(m2, lambda c: c["payload"]["accepted_pairs"][0].__setitem__(1, "101"))))
    attacks.append(("mode2", "m2_12_ambiguous_same_input_two_w", _mutate(m2, lambda c: c["payload"]["accepted_pairs"].append(["001", "0000"]))))

    # --- 12 Mode 3 Domain Attacks ---
    attacks.append(("mode3", "m3_01_overlapping_promise_sets", _mutate(m3, lambda c: c["payload"]["levels"][0]["promise_no"].append("q1_yes"))))
    attacks.append(("mode3", "m3_02_true_witness_not_in_ws", _mutate(m3, lambda c: c["payload"]["levels"][0].__setitem__("true_witness", "missing"))))
    attacks.append(("mode3", "m3_03_ambiguous_yes_query_two_w", _mutate(m3, lambda c: c["payload"]["levels"][0]["verifier"]["q1_yes|w1_bad"].__setitem__("acc_if_0", True))))
    attacks.append(("mode3", "m3_04_promised_no_accepts", _mutate(m3, lambda c: c["payload"]["levels"][0]["verifier"]["q1_no|w1_true"].__setitem__("acc_if_0", True))))
    attacks.append(("mode3", "m3_05_top_depends_on_oop_query", _mutate(m3, lambda c: c["payload"]["top_machine"]["x2"].__setitem__("out_if_0", False))))
    attacks.append(("mode3", "m3_06_wrong_claimed_rounds", _mutate(m3, lambda c: c["payload"].__setitem__("claimed_rounds", 1))))
    attacks.append(("mode3", "m3_07_wrong_final_S", _mutate(m3, lambda c: c["payload"]["claimed_final_S"].__setitem__(0, []))))
    attacks.append(("mode3", "m3_08_false_decoder_matches", _mutate(m3, lambda c: c["payload"].__setitem__("claimed_decoder_matches", False))))
    attacks.append(("mode3", "m3_09_wrong_true_outputs", _mutate(m3, lambda c: c["payload"]["claimed_true_outputs"].__setitem__("x0", False))))
    attacks.append(("mode3", "m3_10_invalid_lower_query_ref", _mutate(m3, lambda c: c["payload"]["levels"][0]["verifier"]["q1_yes|w1_true"].__setitem__("query", "no_such_q"))))
    attacks.append(("mode3", "m3_11_missing_verifier_entry", _mutate(m3, lambda c: c["payload"]["levels"][0]["verifier"].pop("q1_yes|w1_bad"))))
    attacks.append(("mode3", "m3_12_depth_mismatch_levels", _mutate(m3, lambda c: c["payload"].__setitem__("depth", 3))))
    attacks.append(("mode3", "m3_13_int_as_bool_true_outputs", _mutate(m3, lambda c: c["payload"]["claimed_true_outputs"].__setitem__("x0", 1))))
    attacks.append(("mode3", "m3_14_str_as_list_queries", _mutate(m3, lambda c: c["payload"]["levels"][0].__setitem__("queries", "q"))))
    attacks.append(("mode3", "m3_15_int_queries_no_crash", _mutate(m3, lambda c: c["payload"]["levels"][0].__setitem__("queries", 123))))

    # --- 12 Mode 4 Domain Attacks ---
    attacks.append(("mode4", "m4_01_unknown_submode", _mutate(m4_dot, lambda c: c["payload"].__setitem__("submode", "bad_sub"))))
    attacks.append(("mode4", "m4_02_dot_op_R_accepts_v", _mutate(m4_dot, lambda c: c["payload"]["inner_verifier_Rbar"].__setitem__("00|00|10", True))))
    attacks.append(("mode4", "m4_03_dot_op_Rbar_two_vs", _mutate(m4_dot, lambda c: c["payload"]["inner_verifier_Rbar"].__setitem__("00|11|00", True))))
    attacks.append(("mode4", "m4_04_dot_op_wrong_probe_0p", _mutate(m4_dot, lambda c: c["payload"].__setitem__("claimed_probe_refutes_0p", True))))
    attacks.append(("mode4", "m4_05_dot_op_wrong_probe_1p", _mutate(m4_dot, lambda c: c["payload"].__setitem__("claimed_probe_refutes_1p", False))))
    attacks.append(("mode4", "m4_06_single_q_depends_on_oop", _mutate(m4_tag, lambda c: c["payload"]["verifier_if_1"].__setitem__("x0|w0", True))))
    attacks.append(("mode4", "m4_07_single_q_overlapping_prom", _mutate(m4_tag, lambda c: c["payload"]["out_of_promise"].append("q_yes"))))
    attacks.append(("mode4", "m4_08_single_q_wrong_T_size", _mutate(m4_tag, lambda c: c["payload"].__setitem__("claimed_mattering_set_size", 2))))
    attacks.append(("mode4", "m4_09_single_q_wrong_A_size", _mutate(m4_tag, lambda c: c["payload"].__setitem__("claimed_tagged_A_size", 3))))
    attacks.append(("mode4", "m4_10_soup_Y_and_Z_both_accept", _mutate(m4_soup, lambda c: c["payload"]["verifier_Y"].__setitem__("000|01", True))))
    attacks.append(("mode4", "m4_11_soup_wrong_bit", _mutate(m4_soup, lambda c: c["payload"].__setitem__("claimed_soup_bit", 1))))
    attacks.append(("mode4", "m4_12_soup_wrong_witness", _mutate(m4_soup, lambda c: c["payload"].__setitem__("claimed_soup_witness", "01"))))
    attacks.append(("mode4", "m4_13_single_q_nonlist_inputs_no_crash", _mutate(m4_tag, lambda c: c["payload"].__setitem__("inputs", 123))))

    assert len(attacks) == 65, f"Expected 65 attacks, got {len(attacks)}"
    return attacks


def run_red_team_suite() -> Tuple[int, int, List[str]]:
    attacks = build_attacks()
    rejected = 0
    failures: List[str] = []
    for cat, name, payload in attacks:
        ok, _, _ = verify_certificate(payload)
        if not ok:
            rejected += 1
        else:
            failures.append(f"[{cat}] {name} was UNEXPECTEDLY ACCEPTED!")
    return rejected, len(attacks), failures


def main() -> None:
    rejected, total, failures = run_red_team_suite()
    if failures:
        for f in failures:
            print("FAIL:", f)
        sys.exit(1)
    print(f"Adversarial red-team audit: {rejected}/{total} forged payloads REJECTED (100%).")


if __name__ == "__main__":
    main()
