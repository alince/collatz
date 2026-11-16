"""
Unit tests for `collatz_analysis.cs_cegar_redteam` (Track 4: Adversarial 3x3
Counter-Model Falsifier & CEGAR Obstruction Verifier).
"""

from __future__ import annotations

import math
import unittest
from fractions import Fraction
from pathlib import Path

from collatz_analysis.boost_mechanisms import is_surviving_mod1296_class
from collatz_analysis.cs_cegar_redteam import (
    ALL_87_HENSEL_SURVIVORS,
    HENSEL_SURVIVORS_92_TO_95_32,
    HENSEL_SURVIVORS_95_NEW_55,
    audit_bounded_horizon_lyapunov_candidate,
    audit_minimal_counterexample_sieve,
    audit_obstruction_witness,
    audit_positive_cycle_exclusion_predicate,
    audit_track1_wave1_lp_cycles,
    audit_track1_wave2_lp_cycles,
    audit_track1_wave3_lp_cycles,
    audit_track2_wave1_sat_lyapunov,
    audit_track2_wave2_sat_lyapunov,
    audit_track2_wave3_sat_lyapunov,
    audit_track3_wave1_forest_transfer,
    audit_track3_wave2_forest_transfer,
    audit_track3_wave3_forest_transfer,
    audit_universality_gate,
    build_m1_q2_pos_catalog,
    build_m2_z_neg_catalog,
    build_m3_5x1_catalog,
    build_negative_syracuse_tree,
    build_positive_3x1_stress_bank,
    build_sturmian_negative_trajectory,
    generalized_affine_carry,
    int_iter_and_parity,
    is_negative_syracuse_forest_root,
    q2_compressed_step,
    q2_iter_and_parity,
    q2_mod_pow2_pow3,
    q2_v2,
    run_full_redteam_harness,
    trace_q2_cycle_from_parity,
    trace_z_neg_cycle,
    verify_all_weight_primitive_root_mod_pow3,
)


class TestM1Q2PosCounterModel(unittest.TestCase):
    def setUp(self) -> None:
        self.m1 = build_m1_q2_pos_catalog(max_generated_k=9, max_1cycle_w=20)

    def test_canonical_q2_cycles_and_generated_catalog(self) -> None:
        c19 = self.m1["canonical_19_5"]
        c29 = self.m1["canonical_29_5"]
        c1_5 = self.m1["canonical_1_5"]
        c1_125 = self.m1["canonical_1_125"]

        self.assertEqual(c19.x0, Fraction(19, 5))
        self.assertEqual(c19.period_k, 5)
        self.assertEqual(c19.weight_w, 3)
        self.assertEqual(c19.m_blocks, 1)
        self.assertEqual(c19.denom_gap, 5)

        self.assertEqual(c29.x0, Fraction(29, 5))
        self.assertEqual(c29.period_k, 5)
        self.assertEqual(c29.weight_w, 3)
        self.assertEqual(c29.m_blocks, 2)
        self.assertEqual(c29.denom_gap, 5)

        self.assertEqual(c1_5.x0, Fraction(1, 5))
        self.assertEqual(c1_125.x0, Fraction(1, 125))

        # Unique integer primitive cycle up to K = 9 is (1, 0) -> x0 = 2 (or 1 -> (1, 0))
        triv = self.m1["integer_trivial_cycles_found"]
        self.assertEqual(len(triv), 1)
        self.assertIn(triv[0].x0, (Fraction(1, 1), Fraction(2, 1)))

        gen = self.m1["generated_non_integer_cycles"]
        self.assertEqual(len(gen), 96)
        for witness in gen:
            self.assertTrue(witness.is_non_integer)
            self.assertTrue(witness.coprime_to_6)
            self.assertEqual(math.gcd(witness.denom_gap, 6), 1)
            self.assertGreater(witness.min_element, 0)
            end_x, pbits = q2_iter_and_parity(witness.x0, witness.period_k, q=3)
            self.assertEqual(end_x, witness.x0)
            self.assertEqual(pbits, witness.parity_vector)

    def test_m1_hypotheses_hold_vs_fail(self) -> None:
        status = self.m1["hypotheses_status"]
        self.assertTrue(status["positivity_x_gt_0"])
        self.assertTrue(status["affine_decomposition_universal"])
        self.assertTrue(status["bohm_sontacchi_cycle_equation"])
        self.assertTrue(status["negative_drift_2K_gt_3W"])
        self.assertTrue(status["spiral_block_identity"])
        self.assertTrue(status["local_congruences_mod_2A_3B"])
        self.assertTrue(status["entry_merger_algebraic_identity"])

        self.assertFalse(status["z_integrality_at_odd_primes_ge_5"])
        self.assertFalse(status["lower_well_ordering_of_domain"])
        self.assertFalse(status["valuation_archimedean_bound_2_pow_v2_le_x_plus_1"])
        self.assertFalse(status["one_equation_reaches_1"])

        # Verify exact mod 2^A * 3^B well-definedness on 19/5 and 29/5
        r_19_5_mod1296 = q2_mod_pow2_pow3(Fraction(19, 5), 4, 4)
        self.assertIsNotNone(r_19_5_mod1296)
        self.assertEqual((5 * r_19_5_mod1296) % 1296, 19)

        # Verify v_2(19/5 + 1) == 3 and 2^3 = 8 > 24/5 = 19/5 + 1
        self.assertEqual(q2_v2(Fraction(19, 5) + 1), 3)
        self.assertGreater(Fraction(1 << 3, 1), Fraction(19, 5) + 1)


class TestM2ZNegCounterModel(unittest.TestCase):
    def setUp(self) -> None:
        self.m2 = build_m2_z_neg_catalog(sturm_horizons=(20, 40, 80))

    def test_negative_cycles_and_cantor_cone_members(self) -> None:
        c1, c5, c17 = self.m2["cycles"]
        self.assertEqual((c1.seed, c1.period_k, c1.weight_w, c1.denom_gap), (-1, 1, 1, -1))
        self.assertEqual((c5.seed, c5.period_k, c5.weight_w, c5.denom_gap), (-5, 3, 2, -1))
        self.assertEqual((c17.seed, c17.period_k, c17.weight_w, c17.denom_gap), (-17, 11, 7, -139))

        # Every known negative cycle has nonempty Raney S_infty intersection
        self.assertIn(-1, c1.cantor_cone_members)
        self.assertTrue(len(c5.cantor_cone_members) >= 1)
        self.assertTrue(len(c17.cantor_cone_members) >= 1)

        # Signed-non-descending cycle minima satisfy forall k, T^k(x_min) >= x_min in Z
        self.assertEqual(self.m2["signed_non_descending_minima"], (-1, -10, -136))
        for x_min in self.m2["signed_non_descending_minima"]:
            cur = x_min
            for _ in range(25):
                self.assertGreaterEqual(cur, x_min)
                cur = (3 * cur + 1) >> 1 if (cur & 1) else (cur >> 1)

    def test_negative_syracuse_predecessor_trees_and_sturmian_orbits(self) -> None:
        self.assertTrue(is_negative_syracuse_forest_root(-43))
        self.assertFalse(is_negative_syracuse_forest_root(-1))
        self.assertFalse(is_negative_syracuse_forest_root(-5))
        self.assertFalse(is_negative_syracuse_forest_root(-17))

        tree_43 = build_negative_syracuse_tree(-43, max_depth=4)
        self.assertTrue(tree_43["all_edges_exact"])
        # In-degree-0 negative root -43 produces 2^(4+1) - 1 = 31 distinct nodes at depth 4
        self.assertEqual(tree_43["distinct_negative_nodes"], 31)
        self.assertEqual(tree_43["cycle_repeats_detected"], 0)

        # Cycle roots -1 and -5 produce self/cycle repeats inside d in {1..6}
        tree_1 = self.m2["trees"]["-1"]
        tree_5 = self.m2["trees"]["-5"]
        self.assertTrue(tree_1["all_edges_exact"])
        self.assertGreater(tree_1["cycle_repeats_detected"], 0)
        self.assertTrue(tree_5["all_edges_exact"])
        self.assertGreater(tree_5["cycle_repeats_detected"], 0)

        for st in self.m2["sturmian_S_infty_trajectories"]:
            self.assertTrue(st["stays_in_S_infty"])
            self.assertTrue(st["magnitude_grew"])
            self.assertLess(st["x_neg_end"], 0)

        # Backward congruence succeeds on -17, yet quotient y <= -1 fails positivity
        bwd = self.m2["backward_quotient_neg17_witness"]
        self.assertTrue(bwd["congruence_holds_yet_y_negative"])
        self.assertLessEqual(bwd["y_quotient"], -1)


class TestM3FiveXPlusOneCounterModel(unittest.TestCase):
    def setUp(self) -> None:
        self.m3 = build_m3_5x1_catalog(divergent_steps=250)

    def test_positive_cycles_and_divergent_like_orbits(self) -> None:
        c1, c13, c17 = self.m3["positive_cycles"]
        self.assertEqual((c1.seed, c1.period_k, c1.weight_w, c1.denom_gap), (1, 5, 2, 7))
        self.assertEqual((c13.seed, c13.period_k, c13.weight_w, c13.denom_gap), (13, 7, 3, 3))
        self.assertEqual((c17.seed, c17.period_k, c17.weight_w, c17.denom_gap), (17, 7, 3, 3))

        # Minimal non-descending counterexample for 5x+1 is n_min^(5) = 5 -> 13
        pre5 = self.m3["minimal_nondescending_seed_5"]
        self.assertEqual(pre5.classification, "preperiodic_nontrivial")
        self.assertFalse(pre5.reaches_one)
        self.assertFalse(pre5.drops_below_seed)

        # Seed 27 lies on the 17-cycle and never reaches 1
        cyc27 = self.m3["cycle_17_member_27"]
        self.assertEqual(cyc27.classification, "positive_cycle")
        self.assertFalse(cyc27.reaches_one)
        self.assertEqual(cyc27.period_k, 7)

        # Seed 7 (and 21, 31, 55) are divergent-like and never drop below 7
        div7 = self.m3["divergent_like_orbits"][0]
        self.assertEqual(div7.seed, 7)
        self.assertEqual(div7.classification, "divergent_like")
        self.assertFalse(div7.reaches_one)
        self.assertFalse(div7.drops_below_seed)
        self.assertGreater(div7.final_bit_length, 30)

        # 2 is ALSO a primitive root mod 5^w for w >= 1
        self.assertTrue(self.m3["hypotheses_status"]["two_is_primitive_root_mod_q_pow_w"])


class TestPositive3x1StressBankAndCegarGates(unittest.TestCase):
    def test_87_hensel_survivors_mersenne_glides_and_convergents(self) -> None:
        self.assertEqual(len(HENSEL_SURVIVORS_92_TO_95_32), 32)
        self.assertEqual(len(HENSEL_SURVIVORS_95_NEW_55), 55)
        self.assertEqual(len(ALL_87_HENSEL_SURVIVORS), 87)

        stress = build_positive_3x1_stress_bank(mersenne_k_min=10, mersenne_k_max=150)
        self.assertTrue(stress["core_lean_87_exact_match"])
        self.assertTrue(stress["all_87_drop_below_2_pow_71"])
        self.assertEqual(stress["mersenne_count"], 141)
        self.assertTrue(stress["mersenne_all_glide_exact"])
        self.assertEqual(len(stress["mersenne_mod1296_surviving_k"]), 114)
        self.assertTrue(stress["convergent_signs_verified"])
        self.assertGreaterEqual(stress["convergents_count"], 55)

    def test_hard_rule_1_universality_gate(self) -> None:
        ok = audit_universality_gate(
            "UniversalCycleCoprimality",
            axioms_used=("propext", "Classical.choice"),
        )
        self.assertTrue(ok.passed)
        self.assertEqual(ok.verdict, "REDTEAM-PASSED")

        bad_m = audit_universality_gate("FiniteM100Certificate", is_finite_m_table=True)
        self.assertFalse(bad_m.passed)

        bad_w = audit_universality_gate("BoundedWeightW10", is_bounded_weight_table=True)
        self.assertFalse(bad_w.passed)

        bad_ax = audit_universality_gate(
            "LiteratureAxiomDependent",
            axioms_used=("BarinaThreshold", "BakerLMNPowerBound"),
        )
        self.assertFalse(bad_ax.passed)
        self.assertEqual(len(bad_ax.violations), 2)

    def test_hard_rule_2_cycle_exclusion_gate(self) -> None:
        # 1. Naive positive drift gap 2^K > q^W leaks on M1 (19/5) and M3 (13)
        def naive_drift_only(x0: Fraction, bits: tuple[int, ...], q: int) -> bool:
            return x0 > 0 and (1 << len(bits)) > (q ** sum(bits))

        res_drift = audit_positive_cycle_exclusion_predicate("NaiveDriftGap", naive_drift_only)
        self.assertFalse(res_drift.passed)
        self.assertFalse(res_drift.fails_on_m1)
        self.assertFalse(res_drift.fails_on_m3)

        # 2. Z-integrality without x0 > 0 leaks on M2 (-1, -5, -17)
        def z_int_no_sign(x0: Fraction, bits: tuple[int, ...], q: int) -> bool:
            return x0.denominator == 1 and q == 3 and len(bits) >= 1

        res_nosign = audit_positive_cycle_exclusion_predicate("ZIntNoSign", z_int_no_sign)
        self.assertFalse(res_nosign.passed)
        self.assertTrue(res_nosign.fails_on_m1)
        self.assertFalse(res_nosign.fails_on_m2)

        # 3. Positivity + Z-integrality without q == 3 leaks on M3 (5x+1: 13, 17)
        def pos_z_any_q(x0: Fraction, bits: tuple[int, ...], q: int) -> bool:
            return x0 > 0 and x0.denominator == 1 and (1 << len(bits)) > (q ** sum(bits))

        res_any_q = audit_positive_cycle_exclusion_predicate("PosZAnyQ", pos_z_any_q)
        self.assertFalse(res_any_q.passed)
        self.assertTrue(res_any_q.fails_on_m1)
        self.assertTrue(res_any_q.fails_on_m2)
        self.assertFalse(res_any_q.fails_on_m3)

        # 4. Exact trivial-cycle characterization passes all 3 counter-models
        def exact_z_plus_3x1_trivial(x0: Fraction, bits: tuple[int, ...], q: int) -> bool:
            return (
                q == 3
                and x0 > 0
                and x0.denominator == 1
                and x0 in (Fraction(1, 1), Fraction(2, 1))
            )

        res_exact = audit_positive_cycle_exclusion_predicate(
            "ExactTrivialCycle", exact_z_plus_3x1_trivial
        )
        self.assertTrue(res_exact.passed)
        self.assertEqual(res_exact.verdict, "REDTEAM-PASSED")

    def test_hard_rule_2_bounded_horizon_lyapunov_falsifier(self) -> None:
        # Any bounded-horizon ranking function V(x) = log(x + 1) + bounded_mod_bonus
        # is defeated by Mersenne seeds 2^k - 1 in IsSurvivingMod1296Class for k > horizon!
        def shifted_log_potential(x: Fraction, _q: int) -> float:
            val = float(x)
            return math.log(abs(val) + 1.0)

        res_h12 = audit_bounded_horizon_lyapunov_candidate(
            "BoundedHorizon12LogPotential",
            shifted_log_potential,
            horizon_steps=12,
            sieved_mod1296_only=True,
        )
        self.assertFalse(res_h12.passed)
        self.assertFalse(res_h12.holds_on_z_plus)
        self.assertIsNotNone(res_h12.minimal_counterexample)
        self.assertIn("Mersenne seed", str(res_h12.minimal_counterexample))

    def test_minimal_counterexample_sieve_auditor_catches_subtle_bugs(self) -> None:
        # 1. Existing Mod-1296 sieve passes cleanly
        res_1296 = audit_minimal_counterexample_sieve(
            "Mod1296Sieve",
            is_surviving_mod1296_class,
            modulus=1296,
            witness_rules={
                2: (1, ()),  # even -> T^1(n) < n for n >= 2
                1275: (4, (1, 1, 1, 1, 0, 1, 1, 1, 0, 0)),  # 2-stage Garden-of-Eden escape
            },
            min_n_threshold=2,
        )
        self.assertTrue(res_1296["passed"])
        self.assertEqual(res_1296["surviving_count"], 131)

        # 2. Non-contractive (L=5, b=3, 32 > 27) rule on r = 47 mod 144 is caught!
        res_noncontr = audit_minimal_counterexample_sieve(
            "BuggyNonContractiveRule",
            lambda n: (n % 144) != 47,
            modulus=144,
            witness_rules={47: (0, (1, 1, 1, 0, 0))},
            min_n_threshold=2,
        )
        self.assertFalse(res_noncontr["passed"])
        self.assertGreater(len(res_noncontr["rule_failures"]), 0)

        # 3. Small-n carry-offset exception detector:
        # At r = 25 (mod 256), K = 8 has parity vector (1, 0, 1, 1, 0, 0, 1, 1) of weight 5,
        # so 3^5 = 243 < 256 = 2^8 (strictly contractive for all n >= 27!),
        # YET at small n = 25, T^8(25) = 26 > 25!
        res_small_n_bug = audit_minimal_counterexample_sieve(
            "UncheckedSmallNForwardRule",
            lambda n: (n % 256) != 25,
            modulus=256,
            witness_rules={25: (8, ())},
            min_n_threshold=2,
        )
        self.assertFalse(res_small_n_bug["passed"])
        self.assertEqual(len(res_small_n_bug["rule_failures"]), 0)
        self.assertGreater(len(res_small_n_bug["small_n_exceptions"]), 0)
        self.assertEqual(res_small_n_bug["small_n_exceptions"][0][1], 25)

    def test_obstruction_witness_verifier_and_primitive_root_audit(self) -> None:
        # Bounded-modulus LP cycle obstruction witness: 19/5 satisfies all mod 1296 spiral laws
        # yet is NOT in {1, 2}
        w_19_5 = trace_q2_cycle_from_parity((1, 1, 1, 0, 0))
        obs = audit_obstruction_witness(
            "Mod1296RationalPseudoCycleObstruction",
            hypotheses_hold=lambda w: (
                w.x0 > 0
                and w.coprime_to_6
                and q2_iter_and_parity(w.x0, w.period_k)[0] == w.x0
            ),
            target_property_holds=lambda w: w.x0 in (Fraction(1, 1), Fraction(2, 1)),
            witness=w_19_5,
        )
        self.assertTrue(obs.passed)
        self.assertEqual(obs.verdict, "REDTEAM-PASSED")

        # Vacuous/invalid witness is rejected
        bad_obs = audit_obstruction_witness(
            "InvalidVacuousWitness",
            hypotheses_hold=lambda w: w.x0 < 0,
            target_property_holds=lambda w: False,
            witness=w_19_5,
        )
        self.assertFalse(bad_obs.passed)

        prim3 = verify_all_weight_primitive_root_mod_pow3(max_w=7)
        self.assertTrue(prim3["three_adic_lifting_verified"])
        self.assertTrue(prim3["unit_surjectivity_verified"])
        self.assertTrue(prim3["backward_congruence_verified"])
        self.assertIsNone(prim3["q0_nonpositive_y_counterexample"])

    def test_full_harness_and_zero_pii_hygiene(self) -> None:
        full = run_full_redteam_harness()
        self.assertTrue(full["all_baseline_checks_green"])

        # Verify zero PII or local filesystem absolute paths in owned files
        tests_file = Path(__file__).resolve()
        mod_file = tests_file.parent.parent / "cs_cegar_redteam.py"
        win_users_token = "Us" + "ers" + "\\"
        win_users_fwd = "Us" + "ers/"
        unix_home_prefix = "/" + "home" + "/"
        for fpath in (mod_file, tests_file):
            content = fpath.read_text(encoding="utf-8")
            self.assertNotIn(win_users_token, content)
            self.assertNotIn(win_users_fwd, content)
            self.assertNotIn(unix_home_prefix, content)

    def test_track1_wave1_lp_cycles_cegar_audit(self) -> None:
        t1_audit = audit_track1_wave1_lp_cycles()
        self.assertTrue(t1_audit["passed"])
        self.assertEqual(t1_audit["verdict"], "REDTEAM-PASSED")
        self.assertTrue(t1_audit["t1_boundary_ok"])
        self.assertTrue(t1_audit["t2_band_kills_w_le_4"])
        self.assertEqual(t1_audit["sharper_mod48_6classes"], (7, 11, 23, 31, 43, 47))
        self.assertTrue(t1_audit["t3_m1_m2_m3_clean"])
        self.assertTrue(t1_audit["t4_obstruction_ok"])

    def test_track3_wave1_forest_transfer_cegar_audit(self) -> None:
        t3_audit = audit_track3_wave1_forest_transfer()
        self.assertTrue(t3_audit["passed"])
        self.assertEqual(t3_audit["verdict"], "REDTEAM-PASSED")
        self.assertTrue(t3_audit["hensel_87_ok"])
        self.assertTrue(t3_audit["nat_no_underflow_ok"])
        self.assertTrue(t3_audit["coset_balance_ok"])
        self.assertTrue(t3_audit["counter_model_gate_passed"])

    def test_track2_wave1_sat_lyapunov_cegar_audit(self) -> None:
        t2_audit = audit_track2_wave1_sat_lyapunov()
        self.assertTrue(t2_audit["passed"])
        self.assertEqual(t2_audit["verdict"], "REDTEAM-PASSED")
        self.assertTrue(t2_audit["interleaved_srs_ok"])
        self.assertTrue(t2_audit["arctic_k0_ok"])
        self.assertTrue(t2_audit["pumping_ok"])
        self.assertEqual(t2_audit["mod46656_surviving_count"], 2674)
        self.assertTrue(t2_audit["mod46656_sweep_ok"])
        self.assertTrue(t2_audit["empty_head_ok"])
        self.assertTrue(t2_audit["u1_eq_1_w5_ok"])
        self.assertTrue(t2_audit["counter_model_gate_passed"])

    def test_track1_wave2_lp_cycles_cegar_audit(self) -> None:
        t1_w2 = audit_track1_wave2_lp_cycles()
        self.assertTrue(t1_w2["passed"])
        self.assertEqual(t1_w2["verdict"], "REDTEAM-PASSED")
        self.assertTrue(t1_w2["t5_ok"])
        self.assertTrue(t1_w2["t6_ok"])
        self.assertEqual(t1_w2["convergent_squeeze_hits"], 0)
        self.assertTrue(t1_w2["t7_ok"])
        self.assertTrue(t1_w2["t8_ok"])
        self.assertEqual(t1_w2["mod96_8classes"], (7, 31, 47, 59, 71, 79, 91, 95))

    def test_track3_wave2_forest_transfer_cegar_audit(self) -> None:
        t3_w2 = audit_track3_wave2_forest_transfer()
        self.assertTrue(t3_w2["passed"])
        self.assertEqual(t3_w2["verdict"], "REDTEAM-PASSED")
        self.assertTrue(t3_w2["t3_8_excursion_ok"])
        self.assertTrue(t3_w2["t3_9_boundary_ok"])
        self.assertTrue(t3_w2["m1_m2_subcritical_separation_ok"])
        self.assertTrue(t3_w2["t3_10_11_ok"])
        self.assertTrue(t3_w2["t3_12_ok"])
        self.assertTrue(t3_w2["wave2_cert_ok"])

    def test_track2_wave2_sat_lyapunov_cegar_audit(self) -> None:
        falsified_k0 = audit_track2_wave2_sat_lyapunov(require_k_ge_1=False)
        self.assertFalse(falsified_k0["passed"])
        self.assertEqual(falsified_k0["verdict"], "FALSIFIED")
        self.assertTrue(falsified_k0["k0_spurious_detected_at_27"])

        fixed_k1 = audit_track2_wave2_sat_lyapunov(require_k_ge_1=True)
        self.assertTrue(fixed_k1["passed"])
        self.assertEqual(fixed_k1["verdict"], "REDTEAM-PASSED")
        self.assertTrue(fixed_k1["t2_4_ok"])
        self.assertTrue(fixed_k1["t2_5_ok"])
        self.assertTrue(fixed_k1["pumping_373248_ok"])

    def test_track3_wave3_forest_transfer_cegar_audit(self) -> None:
        t3_w3 = audit_track3_wave3_forest_transfer()
        self.assertTrue(t3_w3["passed"])
        self.assertEqual(t3_w3["verdict"], "REDTEAM-PASSED")
        self.assertTrue(t3_w3["t3_16_boundary_ok"])
        self.assertTrue(t3_w3["mersenne_bijection_ok"])
        self.assertTrue(t3_w3["wave3_cert_ok"])

    def test_track2_wave3_sat_lyapunov_cegar_audit(self) -> None:
        t2_w3 = audit_track2_wave3_sat_lyapunov()
        self.assertTrue(t2_w3["passed"])
        self.assertEqual(t2_w3["verdict"], "REDTEAM-PASSED")
        self.assertTrue(t2_w3["t2_7_ok"])
        self.assertTrue(t2_w3["t2_8_ok"])
        self.assertTrue(t2_w3["t2_9_ok"])
        self.assertTrue(t2_w3["gate3_ok"])

    def test_track1_wave3_lp_cycles_cegar_audit(self) -> None:
        t1_w3 = audit_track1_wave3_lp_cycles()
        self.assertTrue(t1_w3["passed"])
        self.assertEqual(t1_w3["verdict"], "REDTEAM-PASSED")
        self.assertTrue(t1_w3["t9_ok"])
        self.assertEqual(t1_w3["conv_17squeeze_hits"], 0)
        self.assertTrue(t1_w3["cubic_gap_ok"])
        self.assertTrue(t1_w3["t10_ok"])
        self.assertTrue(t1_w3["t11_ok"])


if __name__ == "__main__":
    unittest.main()
