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


class TestWave4WholeSpaceAndWitnessBank(unittest.TestCase):
    def test_witness_bank_schema_idempotent_append_and_rejection_gate(self) -> None:
        import shutil
        import tempfile
        from collatz_analysis.cs_cegar_redteam import (
            REQUIRED_WITNESS_DOMAINS,
            append_falsified_hypothesis_record,
            append_witness_to_bank,
            default_witness_bank_path,
            evaluate_hypothesis_against_witness_bank,
            load_witness_bank,
        )

        bank = load_witness_bank()
        self.assertEqual(tuple(bank["domains"].keys()), REQUIRED_WITNESS_DOMAINS)
        self.assertGreaterEqual(len(bank["falsified_hypotheses"]), 6)

        with tempfile.TemporaryDirectory() as tmpdir:
            tmp_bank = Path(tmpdir) / "witness_bank.json"
            shutil.copyfile(default_witness_bank_path(), tmp_bank)

            # Idempotent duplicate witness append returns False; new witness returns True
            self.assertFalse(
                append_witness_to_bank(
                    "z_pos_high_glide",
                    {"witness_id": "ZPOS_N27_MOD373248_MIN", "seed": 27},
                    bank_path=tmp_bank,
                )
            )
            self.assertTrue(
                append_witness_to_bank(
                    "z_pos_high_glide",
                    {"witness_id": "ZPOS_SYNTHETIC_TEST_703", "seed": 703},
                    bank_path=tmp_bank,
                )
            )
            self.assertFalse(
                append_witness_to_bank(
                    "z_pos_high_glide",
                    {"witness_id": "ZPOS_SYNTHETIC_TEST_703", "seed": 703},
                    bank_path=tmp_bank,
                )
            )

            # Invalid domain or empty witness_id raises ValueError
            with self.assertRaises(ValueError):
                append_witness_to_bank("unknown_domain", {"witness_id": "X"}, bank_path=tmp_bank)
            with self.assertRaises(ValueError):
                append_witness_to_bank("z_pos_high_glide", {"witness_id": ""}, bank_path=tmp_bank)

            # Hypothesis failing on M1 is caught and recorded idempotently
            gate_fail = evaluate_hypothesis_against_witness_bank(
                "NaiveDenominatorEq1",
                lambda _dom, e: int(e.get("denominator", 1)) == 1,
                domains=("m1_q2_pos",),
                bank_path=tmp_bank,
                record_failure=True,
                branch="P3",
                statement="All positive cycles have denominator 1.",
            )
            self.assertFalse(gate_fail["passed"])
            self.assertEqual(gate_fail["minimal_failure"], ("m1_q2_pos", "M1_19_OVER_5_ONE_BLOCK"))
            self.assertFalse(
                append_falsified_hypothesis_record(
                    {"hypothesis_id": "NaiveDenominatorEq1", "status": "FALSIFIED"},
                    bank_path=tmp_bank,
                )
            )

            gate_pass = evaluate_hypothesis_against_witness_bank(
                "WitnessIdNonEmpty",
                lambda _dom, e: len(str(e["witness_id"])) > 0,
                bank_path=tmp_bank,
            )
            self.assertTrue(gate_pass["passed"])

    def test_wave4_whole_space_paradigms_and_cousin_benchmark(self) -> None:
        from collatz_analysis.cs_cegar_redteam import (
            core2_pos,
            core3_pos,
            cousin_diamond_phi,
            cousin_diamond_step_int,
            cousin_diamond_step_q6,
            run_wave4_whole_space_campaign,
        )

        # Boundary checks on core2_pos, core3_pos, cousin_diamond_phi, and cousin_diamond_step_q6
        with self.assertRaises(ValueError):
            core3_pos(0)
        with self.assertRaises(ValueError):
            core2_pos(0)
        with self.assertRaises(ValueError):
            cousin_diamond_phi(0)
        with self.assertRaises(ValueError):
            cousin_diamond_step_q6(Fraction(1, 6))

        self.assertEqual(cousin_diamond_step_int(1), 2)
        self.assertEqual(cousin_diamond_step_int(2), 1)
        self.assertEqual(cousin_diamond_step_int(8), 2)

        w4 = run_wave4_whole_space_campaign()
        self.assertTrue(w4["passed"])
        self.assertEqual(w4["verdict"], "REDTEAM-PASSED")
        self.assertTrue(w4["h1_berg_meinardus"]["strictly_gt_one"])
        self.assertTrue(w4["h2_furstenberg"]["hypothesis_falsified"])
        self.assertTrue(w4["h3_pade_and_resultant"]["pade_explosion_verified"])
        self.assertTrue(w4["h3_pade_and_resultant"]["resultant_identities_verified"])
        self.assertTrue(w4["h4_presburger_and_sos"]["one_sided_presburger_hits_pow2_verified"])
        self.assertTrue(w4["h5_cousin_and_synthesis"]["cousin_holdout_verified"])
        self.assertEqual(w4["h5_cousin_and_synthesis"]["true_syracuse_minimal_falsifier_odd"], 17)

    def test_wave4_zero_pii_and_lean4_zero_axioms(self) -> None:
        from collatz_analysis.formal_proofs import (
            ALLOWED_LEAN4_FOUNDATIONAL_AXIOMS,
            verify_lean4_kernel_proofs,
        )

        pkg_dir = Path(__file__).resolve().parent.parent
        win_users_token = "Us" + "ers" + "\\"
        win_users_fwd = "Us" + "ers/"
        unix_home_prefix = "/" + "home" + "/"
        for rel in (
            "PROOF_SPACE_LEDGER.md",
            "witness_bank.json",
            "cs_cegar_redteam.py",
            "CollatzFormal/Wave4WholeSpace.lean",
        ):
            fpath = pkg_dir / rel
            self.assertTrue(fpath.is_file(), f"Missing expected file {rel}")
            txt = fpath.read_text(encoding="utf-8")
            self.assertNotIn(win_users_token, txt)
            self.assertNotIn(win_users_fwd, txt)
            self.assertNotIn(unix_home_prefix, txt)

        res = verify_lean4_kernel_proofs()
        self.assertTrue(res["pure_kernel_verified"])
        self.assertGreaterEqual(res["theorems_audited"], 1379)
        self.assertGreaterEqual(res["axiom_free_theorem_count"], 541)
        ax_map = res["axioms_by_theorem"]
        for thm in (
            "berg_meinardus_radial_hardy_norm_gt_one",
            "berg_meinardus_rational_and_bergman_norm_gt_one",
            "berg_meinardus_weighted_bergman_and_exp_instances",
            "presburger_invariant_separator_collapse",
            "one_sided_presburger_infinite_forward_hits_one",
            "no_one_sided_presburger_divergent_certificate",
            "monotone_ranking_function_r_step_impossibility",
            "two_block_brox_resultant_identities",
            "two_block_quotient_mersenne_gcd_and_mod3_lock",
            "cousin_diamond_phi_strict_descent",
            "cousin_diamond_global_convergence",
            "cousin_diamond_unbounded_mersenne_glide",
            "cousin_diamond_mod_pow2_pow3_potential_impossibility",
            "cousin_diamond_no_finite_dfa_trace_language",
            "cousin_diamond_counter_model_and_antagonism_witnesses",
            "syracuse_laurent_valuation_monomial_impossibility",
            "one_generator_weight_le_five_never_surviving_mod373248",
            "collatz_standard_iff_mod373248_unique_first_hit_weight_ge_six",
            "mod373248_min_weight_six_witness_184111",
        ):
            self.assertIn(thm, ax_map)
            self.assertTrue(
                set(ax_map[thm]).issubset(ALLOWED_LEAN4_FOUNDATIONAL_AXIOMS),
                f"Unexpected custom axiom in {thm}: {ax_map[thm]}",
            )
        self.assertEqual(ax_map["cousin_diamond_counter_model_and_antagonism_witnesses"], [])
        self.assertEqual(ax_map["mod373248_min_weight_six_witness_184111"], [])

    def test_wave4_witness_bank_referential_and_ground_truth_validation(self) -> None:
        import json
        import shutil
        import tempfile
        from collatz_analysis.cs_cegar_redteam import (
            _dynamic_pred_coercive_v2_syracuse,
            _dynamic_pred_core3_syracuse,
            _dynamic_pred_pade_low_degree_extrapolation,
            _dynamic_pred_quadratic_peak_bound,
            _dynamic_pred_sign_blind_cycle_divisibility,
            append_falsified_hypothesis_record,
            default_witness_bank_path,
            evaluate_hypothesis_against_witness_bank,
            load_witness_bank,
            verify_witness_bank_ground_truth,
        )

        truth = verify_witness_bank_ground_truth()
        self.assertTrue(truth["all_witnesses_ground_truth_verified"])
        self.assertEqual(truth["failed_witness_ids"], ())
        self.assertGreaterEqual(truth["verified_witness_count"], 32)

        with tempfile.TemporaryDirectory() as tmpdir:
            tmp_bank = Path(tmpdir) / "witness_bank.json"
            shutil.copyfile(default_witness_bank_path(), tmp_bank)

            # Dangling minimal_witness_id or secondary_witness_id must raise ValueError
            with self.assertRaises(ValueError):
                append_falsified_hypothesis_record(
                    {
                        "hypothesis_id": "DanglingRefTest",
                        "status": "FALSIFIED",
                        "minimal_witness_id": "NON_EXISTENT_WITNESS_ID",
                    },
                    bank_path=tmp_bank,
                )
            with self.assertRaises(ValueError):
                append_falsified_hypothesis_record(
                    {
                        "hypothesis_id": "DanglingSecRefTest",
                        "status": "FALSIFIED",
                        "minimal_witness_id": "ZPOS_N27_MOD373248_MIN",
                        "secondary_witness_id": "NON_EXISTENT_SECONDARY_ID",
                    },
                    bank_path=tmp_bank,
                )

            # Corrupting JSON on disk with dangling ID is caught by load_witness_bank
            corrupted = json.loads(tmp_bank.read_text(encoding="utf-8"))
            corrupted["falsified_hypotheses"].append(
                {
                    "hypothesis_id": "DiskCorruptedHyp",
                    "status": "FALSIFIED",
                    "minimal_witness_id": "MISSING_ID",
                }
            )
            tmp_bank.write_text(json.dumps(corrupted), encoding="utf-8")
            with self.assertRaises(ValueError):
                load_witness_bank(tmp_bank)

            # Dynamic predicates catch brand-new witness IDs purely by mathematical evaluation
            fresh_bank = Path(tmpdir) / "fresh_bank.json"
            base = json.loads(default_witness_bank_path().read_text(encoding="utf-8"))
            base["falsified_hypotheses"] = []
            base["domains"]["z_pos_high_glide"] = [
                {"witness_id": "FRESH_ID_A", "seed": 17, "kills_mechanisms": ["test"]},
                {"witness_id": "FRESH_ID_B", "seed": 9, "kills_mechanisms": ["test"]},
                {"witness_id": "FRESH_ID_C", "seed": 27, "kills_mechanisms": ["test"]},
            ]
            base["domains"]["m2_z_neg"] = [
                {
                    "witness_id": "FRESH_NEG_ID",
                    "seed": -17,
                    "orbit": [-17, -25, -37, -55, -82, -41, -61, -91, -136, -68, -34],
                    "kills_mechanisms": ["test"],
                }
            ]
            base["domains"]["log2_3_convergents"] = [
                {
                    "witness_id": "FRESH_PADE_ID",
                    "a1": "1/3",
                    "a2": "-1/3",
                    "degree_n": 6,
                    "kills_mechanisms": ["test"],
                }
            ]
            fresh_bank.write_text(json.dumps(base), encoding="utf-8")

            r1 = evaluate_hypothesis_against_witness_bank(
                "FreshCore3", _dynamic_pred_core3_syracuse, ("z_pos_high_glide",), fresh_bank
            )
            self.assertEqual(r1["minimal_failure"], ("z_pos_high_glide", "FRESH_ID_A"))
            r2 = evaluate_hypothesis_against_witness_bank(
                "FreshCoerciveV2", _dynamic_pred_coercive_v2_syracuse, ("z_pos_high_glide",), fresh_bank
            )
            self.assertEqual(r2["minimal_failure"], ("z_pos_high_glide", "FRESH_ID_B"))
            r3 = evaluate_hypothesis_against_witness_bank(
                "FreshQuadPeak", _dynamic_pred_quadratic_peak_bound, ("z_pos_high_glide",), fresh_bank
            )
            self.assertEqual(r3["minimal_failure"], ("z_pos_high_glide", "FRESH_ID_C"))
            r4 = evaluate_hypothesis_against_witness_bank(
                "FreshSignBlind", _dynamic_pred_sign_blind_cycle_divisibility, ("m2_z_neg",), fresh_bank
            )
            self.assertEqual(r4["minimal_failure"], ("m2_z_neg", "FRESH_NEG_ID"))
            r5 = evaluate_hypothesis_against_witness_bank(
                "FreshPade", _dynamic_pred_pade_low_degree_extrapolation, ("log2_3_convergents",), fresh_bank
            )
            self.assertEqual(r5["minimal_failure"], ("log2_3_convergents", "FRESH_PADE_ID"))

    def test_wave4_pade_folded_basis_and_boundary_guards(self) -> None:
        import decimal
        from collatz_analysis.cs_cegar_redteam import (
            _dec_neg_log1m,
            _solve_folded_symmetric_type2_diag,
            _solve_type1_and_type2_hermite_pade,
        )

        # Domain boundary guards
        for bad_a in (Fraction(1, 1), Fraction(-1, 1), Fraction(3, 2)):
            with self.assertRaises(ValueError):
                _dec_neg_log1m(bad_a)
        with self.assertRaises(ValueError):
            _solve_type1_and_type2_hermite_pade(Fraction(1, 3), Fraction(-1, 3), 0)
        with self.assertRaises(ValueError):
            _solve_type1_and_type2_hermite_pade(Fraction(0, 1), Fraction(1, 3), 2)
        with self.assertRaises(ValueError):
            _solve_type1_and_type2_hermite_pade(Fraction(1, 3), Fraction(1, 3), 2)

        # High-|a| precision check at a = 9/10 (-log(1/10) = log(10)) where 1200-term series truncated
        with decimal.localcontext() as ctx:
            ctx.prec = 120
            ln10 = decimal.Decimal(10).ln()
            val_9_10 = _dec_neg_log1m(Fraction(9, 10), prec=120)
            self.assertLess(abs(val_9_10 - ln10), decimal.Decimal(10) ** (-115))

        # Folded symmetric {2,3}-smooth basis (1/3, -1/3): low-degree diagonal < 0, step-line & n=55 > 0
        sym6 = _solve_type1_and_type2_hermite_pade(Fraction(1, 3), Fraction(-1, 3), 6)
        self.assertLess(sym6["type2_err_log2"], -9.9)
        self.assertGreater(sym6["type2_offdiag_n1_n_err_log2"], 10.0)
        self.assertTrue(sym6["stepline_casorati_det_nonzero"])
        sym55 = _solve_folded_symmetric_type2_diag(Fraction(1, 3), 55)
        self.assertGreater(sym55["err_log2"], 7.0)

    def test_wave4_exact_ast_large_int_laurent_barrier_and_backward_tree(self) -> None:
        from collatz_analysis.cs_cegar_redteam import (
            _eval_nonlocal_ast,
            audit_syracuse_laurent_valuation_monomial_barrier,
            cousin_diamond_step_int,
            synthesize_and_redteam_backward_quotient_tree_invariants,
            synthesize_nonlocal_cousin_invariant_and_redteam_collatz,
        )

        # Regression test for 2048-bit saturation bug at x = 1 << 260
        legacy_deg4_ast = ("sq", ("sq", ("mul", ("x",), ("c3_xp1",))))
        big_x = 1 << 260
        self.assertLess(
            _eval_nonlocal_ast(legacy_deg4_ast, cousin_diamond_step_int(big_x)),
            _eval_nonlocal_ast(legacy_deg4_ast, big_x),
        )
        syn = synthesize_nonlocal_cousin_invariant_and_redteam_collatz()
        self.assertEqual(syn["cousin_synthesized_node_count"], 3)
        self.assertLess(
            _eval_nonlocal_ast(syn["cousin_synthesized_ast"], cousin_diamond_step_int(big_x)),
            _eval_nonlocal_ast(syn["cousin_synthesized_ast"], big_x),
        )

        laurent = audit_syracuse_laurent_valuation_monomial_barrier(max_abs_exp=6)
        self.assertTrue(laurent["laurent_monomial_barrier_verified"])
        self.assertEqual(laurent["laurent_surviving_triples"], 0)

        tree = synthesize_and_redteam_backward_quotient_tree_invariants()
        self.assertTrue(tree["mod512_nine_step_weight_ge6_verified"])
        self.assertTrue(tree["weight_le_5_mod373248_disjoint_verified"])
        self.assertTrue(tree["sharp_weight_6_witness_184111_verified"])
        self.assertTrue(tree["q_ray_strict_growth_verified"])
        self.assertTrue(tree["backward_tree_y_monotone_falsified"])


class TestWave5WholeSpaceCampaign(unittest.TestCase):
    def test_wave5_campaign_all_four_fronts_and_witness_bank(self) -> None:
        from collatz_analysis.cs_cegar_redteam import (
            audit_w5_front_a_nonradial_preimage_superharmonicity,
            audit_w5_front_b_cousin_diamond2_multiterm_and_nontri_matrices,
            audit_w5_front_c_beukers_rhin_mblock_and_antipodal_primes,
            audit_w5_front_d_coupled_q_rays_and_pi2_calibration,
            run_wave5_whole_space_campaign,
        )

        w5 = run_wave5_whole_space_campaign()
        self.assertTrue(w5["passed"])
        self.assertEqual(w5["verdict"], "REDTEAM-PASSED")
        self.assertTrue(w5["witness_bank_ground_truth_verified"])
        self.assertGreaterEqual(w5["witness_bank_total_entries"], 41)
        self.assertGreaterEqual(w5["witness_bank_falsified_count"], 12)

        fa = audit_w5_front_a_nonradial_preimage_superharmonicity()
        self.assertTrue(fa["barrier_verified"])
        self.assertTrue(fa["stopping_time_model_contraction_verified"])
        self.assertTrue(fa["z_j_valuation_constancy_verified"])
        self.assertTrue(fa["z_j_modular_repetition_verified"])

        fb = audit_w5_front_b_cousin_diamond2_multiterm_and_nontri_matrices()
        self.assertTrue(fb["cousin_diamond2_global_descent_verified"])
        self.assertTrue(fb["cousin_diamond2_syracuse_witnesses_verified"])
        self.assertEqual(fb["cousin_diamond2_single_laurent_survivors"], 0)
        self.assertTrue(fb["cousin_diamond2_countermodels_verified"])
        self.assertTrue(fb["cousin_diamond2_q6_matches_int_verified"])
        self.assertTrue(fb["two_term_w4_trap_and_rebound_falsifier_verified"])
        self.assertTrue(fb["non_triangular_sandwich_collapse_verified"])

        fc = audit_w5_front_c_beukers_rhin_mblock_and_antipodal_primes()
        self.assertTrue(fc["beukers_rhin_explosion_verified"])
        self.assertTrue(fc["beukers_rhin_series_cross_verified"])
        self.assertTrue(fc["mblock_resultant_identities_verified"])
        self.assertTrue(fc["one_block_even_even_impossible_verified"])
        self.assertEqual(fc["antipodal_prime_count_lt_300"], 28)
        self.assertTrue(fc["antipodal_primes_and_m1_separation_verified"])

        fd = audit_w5_front_d_coupled_q_rays_and_pi2_calibration()
        self.assertTrue(fd["q_ray_affine_and_382_per_729_verified"])
        self.assertTrue(fd["q_pos_universal_first_hit_verified"])
        self.assertTrue(fd["length_le_7_mod373248_disjoint_verified"])
        self.assertTrue(fd["pi2_skolem_box_and_cousin_poly_bound_verified"])

    def test_wave5_boundary_guards_and_synthetic_dynamic_predicates(self) -> None:
        import json
        import tempfile
        from collatz_analysis.cs_cegar_redteam import (
            _beukers_rhin_2d_beta_series,
            _dynamic_pred_antipodal_prime_without_z_integrality,
            _dynamic_pred_beukers_rhin_const_elim_converges,
            _dynamic_pred_cousin_diamond2_omits_odd_pow3_cone,
            _dynamic_pred_glide_laurent_2term_syracuse,
            _dynamic_pred_periodic_valuation_decay,
            _dynamic_pred_pos_2term_valuation_syracuse,
            _solve_beukers_rhin_2d_and_const_elimination,
            cousin_diamond2_phi,
            cousin_diamond2_step_int,
            cousin_diamond2_step_q6,
            default_witness_bank_path,
            evaluate_hypothesis_against_witness_bank,
        )

        # Explicit boundary & error-path checks
        for bad_q in (0, -3, 2, 4):
            with self.assertRaises(ValueError):
                cousin_diamond2_step_int(7, q=bad_q)
        for bad_frac in (Fraction(1, 2), Fraction(1, 3), Fraction(5, 6)):
            with self.assertRaises(ValueError):
                cousin_diamond2_step_q6(bad_frac)
        for bad_x in (0, -1, -5):
            with self.assertRaises(ValueError):
                cousin_diamond2_phi(bad_x)
        with self.assertRaises(ValueError):
            _solve_beukers_rhin_2d_and_const_elimination(0)
        with self.assertRaises(ValueError):
            _beukers_rhin_2d_beta_series(0)
        with self.assertRaises(ValueError):
            _beukers_rhin_2d_beta_series(1, terms=0)
        with self.assertRaises(ValueError):
            _beukers_rhin_2d_beta_series(1, prec=10)

        # Regression checks for 2D Euler-Rhin integral solver vs exact Beta series (including n > 6)
        br1 = _solve_beukers_rhin_2d_and_const_elimination(1)
        br5 = _solve_beukers_rhin_2d_and_const_elimination(5)
        br7 = _solve_beukers_rhin_2d_and_const_elimination(7)
        br8 = _solve_beukers_rhin_2d_and_const_elimination(8)
        self.assertGreater(br1["symbolic_vs_series_diff"], 0.0)
        self.assertLess(br1["symbolic_vs_series_diff"], 1e-40)
        self.assertGreater(br5["symbolic_vs_series_diff"], 0.0)
        self.assertLess(br5["symbolic_vs_series_diff"], 1e-40)
        self.assertGreater(br7["symbolic_vs_series_diff"], 0.0)
        self.assertLess(br7["symbolic_vs_series_diff"], 1e-40)
        self.assertGreater(br8["symbolic_vs_series_diff"], 0.0)
        self.assertLess(br8["symbolic_vs_series_diff"], 1e-40)
        self.assertGreater(br1["integral_2d_log2"], -6.4)
        self.assertLess(br1["integral_2d_log2"], -6.2)
        self.assertGreater(br5["integral_2d_log2"], -27.9)
        self.assertLess(br5["integral_2d_log2"], -27.7)
        self.assertGreater(br1["nonsep_2d_err_log2"], 3.4)
        self.assertLess(br1["nonsep_2d_err_log2"], 3.5)
        self.assertGreater(br5["nonsep_2d_err_log2"], 18.5)
        self.assertLess(br5["nonsep_2d_err_log2"], 18.6)

        # Edge values, x = 53 = 2*3^3 - 1 regression, & large-bit inputs on T_diamond2
        self.assertEqual(cousin_diamond2_step_int(0), 0)
        self.assertEqual(cousin_diamond2_step_int(1), 2)
        self.assertEqual(cousin_diamond2_step_int(2), 1)
        self.assertEqual(cousin_diamond2_step_int(-1), -1)
        self.assertEqual(cousin_diamond2_step_int(53), 40)
        self.assertEqual(cousin_diamond2_step_q6(Fraction(53, 1)), Fraction(40, 1))
        big = (1 << 250) - 1
        self.assertLess(cousin_diamond2_phi(cousin_diamond2_step_int(big)), cousin_diamond2_phi(big))

        # Dynamic witness-bank predicates on brand-new synthetic witness IDs
        with tempfile.TemporaryDirectory() as tmpdir:
            fresh_bank = Path(tmpdir) / "fresh_w5_bank.json"
            base = json.loads(default_witness_bank_path().read_text(encoding="utf-8"))
            base["falsified_hypotheses"] = []
            base["domains"]["z_pos_high_glide"] = [
                {
                    "witness_id": "SYNTH_SPINE_Z",
                    "seed": 85,
                    "sibling_seed": 5461,
                    "kills_mechanisms": ["test"],
                },
                {
                    "witness_id": "SYNTH_POS2_3",
                    "seed": 3,
                    "kills_mechanisms": ["test"],
                },
                {
                    "witness_id": "SYNTH_REBOUND_13",
                    "seed": 13,
                    "kills_mechanisms": ["test"],
                },
                {
                    "witness_id": "SYNTH_ODD_POW3_53",
                    "seed": 53,
                    "cousin_diamond2_next": 40,
                    "kills_mechanisms": ["test"],
                },
            ]
            base["domains"]["m1_q2_pos"] = [
                {
                    "witness_id": "SYNTH_M1_211_13",
                    "x0": "211/13",
                    "m_blocks": 1,
                    "period_k": 8,
                    "weight_w": 5,
                    "kills_mechanisms": ["test"],
                }
            ]
            base["domains"]["log2_3_convergents"] = [
                {
                    "witness_id": "SYNTH_BR_N5",
                    "beukers_degree_n": 5,
                    "kills_mechanisms": ["test"],
                }
            ]
            fresh_bank.write_text(json.dumps(base), encoding="utf-8")

            r_sp = evaluate_hypothesis_against_witness_bank(
                "SynthSpine", _dynamic_pred_periodic_valuation_decay, ("z_pos_high_glide",), fresh_bank
            )
            self.assertEqual(r_sp["minimal_failure"], ("z_pos_high_glide", "SYNTH_SPINE_Z"))

            r_p2 = evaluate_hypothesis_against_witness_bank(
                "SynthPos2", _dynamic_pred_pos_2term_valuation_syracuse, ("z_pos_high_glide",), fresh_bank
            )
            self.assertEqual(r_p2["minimal_failure"], ("z_pos_high_glide", "SYNTH_POS2_3"))

            r_2t = evaluate_hypothesis_against_witness_bank(
                "SynthTwoTerm", _dynamic_pred_glide_laurent_2term_syracuse, ("z_pos_high_glide",), fresh_bank
            )
            self.assertEqual(r_2t["minimal_failure"], ("z_pos_high_glide", "SYNTH_REBOUND_13"))

            r_53 = evaluate_hypothesis_against_witness_bank(
                "SynthOddPow3", _dynamic_pred_cousin_diamond2_omits_odd_pow3_cone, ("z_pos_high_glide",), fresh_bank
            )
            self.assertEqual(r_53["minimal_failure"], ("z_pos_high_glide", "SYNTH_ODD_POW3_53"))

            r_m1 = evaluate_hypothesis_against_witness_bank(
                "SynthM1Ant", _dynamic_pred_antipodal_prime_without_z_integrality, ("m1_q2_pos",), fresh_bank
            )
            self.assertEqual(r_m1["minimal_failure"], ("m1_q2_pos", "SYNTH_M1_211_13"))

            r_br = evaluate_hypothesis_against_witness_bank(
                "SynthBeukers", _dynamic_pred_beukers_rhin_const_elim_converges, ("log2_3_convergents",), fresh_bank
            )
            self.assertEqual(r_br["minimal_failure"], ("log2_3_convergents", "SYNTH_BR_N5"))

            # Domain validation guards & disk-safety on invalid kills_mechanisms
            from collatz_analysis.cs_cegar_redteam import (
                append_witness_to_bank,
                load_witness_bank,
                verify_witness_bank_ground_truth,
            )

            with self.assertRaises(ValueError):
                evaluate_hypothesis_against_witness_bank("EmptyDom", lambda _d, _e: True, (), fresh_bank)
            with self.assertRaises(ValueError):
                evaluate_hypothesis_against_witness_bank("BadDom", lambda _d, _e: True, ("bad_dom",), fresh_bank)

            clean_copy = Path(tmpdir) / "clean_copy.json"
            clean_copy.write_text(default_witness_bank_path().read_text(encoding="utf-8"), encoding="utf-8")
            before_zpos_len = len(load_witness_bank(clean_copy)["domains"]["z_pos_high_glide"])
            self.assertGreaterEqual(before_zpos_len, 14)
            with self.assertRaises(ValueError):
                append_witness_to_bank(
                    "z_pos_high_glide",
                    {"witness_id": "BAD_EMPTY_KILLS", "seed": 5, "kills_mechanisms": []},
                    bank_path=clean_copy,
                )
            # Disk copy remains loadable and uncorrupted after rejected append
            self.assertEqual(len(load_witness_bank(clean_copy)["domains"]["z_pos_high_glide"]), before_zpos_len)

            # Corrupting v3_seed_plus_1, x1, m_blocks, carry, claimless entries, or unknown keys fails ground-truth
            corrupt_data = json.loads(default_witness_bank_path().read_text(encoding="utf-8"))
            corrupt_data["domains"]["z_pos_high_glide"][2]["v3_seed_plus_1"] = 999999
            corrupt_data["domains"]["z_pos_high_glide"].append(
                {"witness_id": "CLAIMLESS_ZPOS", "seed": 5, "kills_mechanisms": ["none"]}
            )
            corrupt_data["domains"]["z_pos_high_glide"].append(
                {
                    "witness_id": "UNKNOWN_KEY_ZPOS",
                    "seed": 8,
                    "next_compressed": 4,
                    "unverified_extra_field": 123,
                    "kills_mechanisms": ["none"],
                }
            )
            corrupt_data["domains"]["m1_q2_pos"][2]["x1"] = "999999/13"
            corrupt_data["domains"]["m1_q2_pos"][8]["m_blocks"] = 999999
            corrupt_data["domains"]["m2_z_neg"][2]["carry"] = 999999
            corrupt_path = Path(tmpdir) / "corrupt_gt.json"
            corrupt_path.write_text(json.dumps(corrupt_data), encoding="utf-8")
            gt_bad = verify_witness_bank_ground_truth(corrupt_path)
            self.assertFalse(gt_bad["all_witnesses_ground_truth_verified"])
            for expected_failed_id in (
                "ZPOS_EVEN_PEAK_8_TO_4_V3_WIPEOUT",
                "CLAIMLESS_ZPOS",
                "UNKNOWN_KEY_ZPOS",
                "M1_251_OVER_13_POTENTIAL",
                "M1_211_OVER_13_ONE_BLOCK_D13",
                "M2_NEG17_NONUNIT_11CYCLE",
            ):
                self.assertIn(expected_failed_id, gt_bad["failed_witness_ids"])

    def test_wave5_zero_pii_and_lean4_zero_custom_axioms(self) -> None:
        import re
        from collatz_analysis.formal_proofs import (
            ALLOWED_LEAN4_FOUNDATIONAL_AXIOMS,
            verify_lean4_kernel_proofs,
        )

        pkg_dir = Path(__file__).resolve().parent.parent
        win_users_token = "Us" + "ers" + "\\"
        win_users_fwd = "Us" + "ers/"
        unix_home_prefix = "/" + "home" + "/"
        win_drive_bs = "C:" + "\\"
        win_drive_fs = "C:" + "/"
        audited_file_count = 0
        for fpath in sorted(pkg_dir.rglob("*")):
            if ".lake" in fpath.parts or "__pycache__" in fpath.parts or not fpath.is_file():
                continue
            if fpath.suffix not in (".py", ".lean", ".md", ".json", ".c"):
                continue
            audited_file_count += 1
            txt = fpath.read_text(encoding="utf-8")
            rel = str(fpath.relative_to(pkg_dir))
            self.assertNotIn(win_users_token, txt, f"PII path token in {rel}")
            self.assertNotIn(win_users_fwd, txt, f"PII path token in {rel}")
            self.assertNotIn(unix_home_prefix, txt, f"PII path token in {rel}")
            self.assertNotIn(win_drive_bs, txt, f"Drive path token in {rel}")
            self.assertNotIn(win_drive_fs, txt, f"Drive path token in {rel}")
        self.assertGreaterEqual(audited_file_count, 75)

        res = verify_lean4_kernel_proofs()
        self.assertTrue(res["pure_kernel_verified"])
        self.assertGreaterEqual(len(res["lean_files"]), 54)
        self.assertGreaterEqual(res["theorems_audited"], 1517)
        self.assertGreaterEqual(res["axiom_free_theorem_count"], 547)
        self.assertTrue(any(Path(p).name == "Wave5WholeSpace.lean" for p in res["lean_files"]))
        ax_map = res["axioms_by_theorem"]
        w5_theorems = (
            "nat_valued_preimage_weight_impossibility",
            "preimage_superharmonic_rational_eliminates_all_cycles",
            "strictly_contractive_bounded_preimage_weight_implies_collatz_standard",
            "berg_meinardus_periodic_valuation_weight_impossibility",
            "all_dim_coord_monotone_non_triangular_impossibility",
            "cousin_diamond2_phi_strict_descent",
            "cousin_diamond2_global_convergence",
            "cousinDiamond2StepInt_ofNat_eq",
            "cousin_diamond2_unbounded_glide_and_mod_barrier",
            "cousin_diamond2_single_laurent_monomial_impossibility",
            "cousin_diamond2_counter_model_separation",
            "two_term_valuation_sum_survives_w4_witnesses_yet_fails_syracuse",
            "syracuse_multiterm_laurent_valuation_impossibility",
            "preimage_weight_induces_strict_syracuse_lyapunov",
            "berg_meinardus_reciprocal_multiterm_laurent_impossibility",
            "broxSpiralCarry_eq_affineCarry_universal",
            "m_block_brox_resultant_and_quotient_locks",
            "m_block_cycle_induces_brox_quotients",
            "one_block_even_even_impossibility",
            "one_block_antipodal_order_divisor_exclusion",
            "one_block_antipodal_prime_instances_and_m1_separation",
            "exactBackwardQuotient_one_ray_step_law",
            "one_generator_q_pos_always_first_hit",
            "mod373248_ray_dyadic_pinning_and_triadic_bijection",
            "one_generator_length_le_seven_never_surviving_mod373248",
            "collatz_standard_iff_mod373248_unique_first_hit_len_ge_eight",
            "pi2_skolem_box_equivalence_and_cousin_polynomial_stopping_bound",
        )
        for thm in w5_theorems:
            self.assertIn(thm, ax_map)
            self.assertTrue(
                set(ax_map[thm]).issubset(ALLOWED_LEAN4_FOUNDATIONAL_AXIOMS),
                f"Unexpected custom axiom in {thm}: {ax_map[thm]}",
            )
        # Verify literally []-axiom ground/separation theorems and choice-free theorems
        self.assertEqual(ax_map["cousin_diamond2_counter_model_separation"], [])
        self.assertEqual(ax_map["two_term_valuation_sum_survives_w4_witnesses_yet_fails_syracuse"], [])
        self.assertEqual(ax_map["survivingMod512Bool_nine_gt_seven_weight_grid"], [])
        for choice_free_thm in (
            "nat_valued_preimage_weight_impossibility",
            "cousin_diamond2_single_laurent_monomial_impossibility",
            "broxSpiralCarry_eq_affineCarry_universal",
            "m_block_brox_resultant_and_quotient_locks",
            "m_block_cycle_induces_brox_quotients",
            "one_block_even_even_impossibility",
        ):
            self.assertNotIn("Classical.choice", ax_map[choice_free_thm])
        # Verify no Wave5 docstring falsely claims (`[]` axioms) on a non-empty-axiom theorem
        w5_src = (pkg_dir / "CollatzFormal/Wave5WholeSpace.lean").read_text(encoding="utf-8")
        for doc, thm_name in re.findall(r"/--\s*(.*?)\s*-/\s*theorem\s+([A-Za-z0-9_']+)\b", w5_src, flags=re.S):
            if "`[]` axioms" in doc:
                self.assertEqual(ax_map.get(thm_name), [], f"False []-axiom docstring on {thm_name}")

    def test_cli_summary_and_trajectory_include_wave5_loop(self) -> None:
        import contextlib
        import io
        from collatz_analysis.cli import main as cli_main

        # 1. Trajectory mode boundary (n = 1) and nontrivial excursion (n = 27)
        buf_t1 = io.StringIO()
        with contextlib.redirect_stdout(buf_t1):
            rc_t1 = cli_main(["--trajectory", "1"])
        self.assertEqual(rc_t1, 0)
        self.assertIn("=== Trajectory Analysis for n = 1 ===", buf_t1.getvalue())
        self.assertIn("Total stopping time sigma_inf: 0", buf_t1.getvalue())

        buf_t27 = io.StringIO()
        with contextlib.redirect_stdout(buf_t27):
            rc_t27 = cli_main(["--trajectory", "27"])
        self.assertEqual(rc_t27, 0)
        self.assertIn("=== Trajectory Analysis for n = 27 ===", buf_t27.getvalue())
        self.assertIn("Total stopping time sigma_inf: 70", buf_t27.getvalue())

        # 2. Boundary error paths on non-positive trajectory / dp-depth & conflicting CLI flags
        for bad_n in ("0", "-5"):
            with self.assertRaises(ValueError):
                with contextlib.redirect_stdout(io.StringIO()):
                    cli_main(["--trajectory", bad_n])
        with self.assertRaises(ValueError):
            with contextlib.redirect_stdout(io.StringIO()):
                cli_main(["--summary", "--dp-depth", "0"])
        for bad_argv in (
            ["--summary", "--trajectory", "27"],
            ["--trajectory", "27", "--dp-depth", "50"],
            ["--trajectory", "27", "--full-m95"],
            ["--unknown-flag"],
        ):
            with self.assertRaises(SystemExit) as cm:
                with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                    cli_main(bad_argv)
            self.assertEqual(cm.exception.code, 2)

        # 3. Full --summary run includes both Wave 4 and Wave 5 Whole-Space Proof Loop sections
        buf_sum = io.StringIO()
        with contextlib.redirect_stdout(buf_sum):
            rc_sum = cli_main(["--summary", "--dp-depth", "50"])
        self.assertEqual(rc_sum, 0)
        out = buf_sum.getvalue()
        self.assertEqual(out.count("Depth k =  50:"), 1)
        self.assertIn("[Wave 4 Whole-Space Proof Loop]", out)
        self.assertIn("[Wave 5 Whole-Space Proof Loop]", out)
        self.assertIn(
            "u-gate=True, ground-truth=True, verdict=REDTEAM-PASSED",
            out,
        )
        self.assertIn(
            "A=True, T_diamond2=True (1-term=0), 2-term/non-tri=True",
            out,
        )
        self.assertIn(
            "2D/m-blk=True, antipodal=True (28 primes<300), q-ray/|u|>=8/Pi2=True",
            out,
        )
        self.assertLess(
            out.index("[Wave 4 Whole-Space Proof Loop]"),
            out.index("[Wave 5 Whole-Space Proof Loop]"),
        )
        self.assertLess(
            out.index("[Wave 5 Whole-Space Proof Loop]"),
            out.index("[Lean 4 Kernel Verification]"),
        )

        # 4. Verify lean_available == False fallback output and non-zero exit code on failed gates
        from unittest import mock

        buf_nolean = io.StringIO()
        with mock.patch(
            "collatz_analysis.cli.verify_lean4_kernel_proofs",
            return_value={"lean_available": False, "static_hygiene_clean": True},
        ), contextlib.redirect_stdout(buf_nolean):
            rc_nolean = cli_main(["--summary", "--dp-depth", "10"])
        self.assertEqual(rc_nolean, 0)
        self.assertIn(
            "Lean 4 toolchain not found on PATH / ~/.elan/bin (static hygiene clean: True)",
            buf_nolean.getvalue(),
        )

        failed_w5 = {
            "passed": False,
            "verdict": "FALSIFIED",
            "universality_gate_passed": True,
            "witness_bank_total_entries": 41,
            "witness_bank_falsified_count": 12,
            "witness_bank_ground_truth_verified": True,
            "front_a_preimage_superharmonicity": {"barrier_verified": True},
            "front_b_cousin_diamond2_and_cones": {
                "cousin_diamond2_global_descent_verified": True,
                "cousin_diamond2_syracuse_witnesses_verified": False,
                "cousin_diamond2_single_laurent_impossible_verified": True,
                "cousin_diamond2_single_laurent_survivors": 0,
                "cousin_diamond2_countermodels_verified": True,
                "two_term_w4_trap_and_rebound_falsifier_verified": True,
                "non_triangular_sandwich_collapse_verified": True,
            },
            "front_c_beukers_rhin_and_resultants": {
                "beukers_rhin_explosion_verified": True,
                "beukers_rhin_series_cross_verified": False,
                "mblock_resultant_identities_verified": True,
                "one_block_even_even_impossible_verified": True,
                "antipodal_primes_and_m1_separation_verified": True,
                "antipodal_prime_count_lt_300": 28,
            },
            "front_d_coupled_q_rays_and_pi2": {
                "q_ray_affine_and_382_per_729_verified": True,
                "q_pos_universal_first_hit_verified": True,
                "length_le_7_mod373248_disjoint_verified": True,
                "pi2_skolem_box_and_cousin_poly_bound_verified": True,
            },
        }
        buf_fail = io.StringIO()
        with mock.patch(
            "collatz_analysis.cs_cegar_redteam.run_wave5_whole_space_campaign",
            return_value=failed_w5,
        ), mock.patch(
            "collatz_analysis.cli.verify_lean4_kernel_proofs",
            return_value={"lean_available": False, "static_hygiene_clean": True},
        ), contextlib.redirect_stdout(buf_fail):
            rc_fail = cli_main(["--summary", "--dp-depth", "10"])
        self.assertEqual(rc_fail, 1)
        self.assertIn("T_diamond2=False", buf_fail.getvalue())
        self.assertIn("2D/m-blk=False", buf_fail.getvalue())


class TestWave6WholeSpaceCampaign(unittest.TestCase):
    def test_wave6_campaign_all_four_fronts_full_suite_and_witness_bank(self) -> None:
        import collatz_analysis as ca
        from collatz_analysis.cs_cegar_redteam import (
            audit_w6_front_a_coupled_core_preimage_barrier,
            audit_w6_front_b_zero_diag_block_return_and_cousin_diamond3,
            audit_w6_front_c_laurent_determinants_and_2block_locks,
            audit_w6_front_d_cross_ray_disjointness_and_prefix_covering,
            load_witness_bank,
            run_wave6_whole_space_campaign,
        )

        for exported_sym in (
            "is_diamond3_cone4",
            "cousin_diamond3_step_int",
            "cousin_diamond3_step_q6",
            "cousin_diamond3_block_return",
            "spiral_block_return_int",
            "audit_w6_front_a_coupled_core_preimage_barrier",
            "audit_w6_front_b_zero_diag_block_return_and_cousin_diamond3",
            "audit_w6_front_c_laurent_determinants_and_2block_locks",
            "audit_w6_front_d_cross_ray_disjointness_and_prefix_covering",
            "run_wave6_whole_space_campaign",
        ):
            self.assertTrue(hasattr(ca, exported_sym), f"Missing package export: {exported_sym}")

        bank = load_witness_bank()
        self.assertEqual(len(bank["domains"]["z_pos_high_glide"]), 17)

        w6 = run_wave6_whole_space_campaign()
        self.assertTrue(w6["passed"])
        self.assertEqual(w6["verdict"], "REDTEAM-PASSED")
        self.assertTrue(w6["universality_gate_passed"])
        self.assertTrue(w6["witness_bank_ground_truth_verified"])
        self.assertGreaterEqual(w6["witness_bank_total_entries"], 47)
        self.assertGreaterEqual(w6["witness_bank_falsified_count"], 16)

        fa = audit_w6_front_a_coupled_core_preimage_barrier()
        self.assertTrue(fa["coupled_core_spine_sum_lt_1e_3"])
        self.assertTrue(fa["coupled_core_survives_17_97_169_fails_7_verified"])
        self.assertEqual(fa["effective_degree_cone_survivors"], 0)
        self.assertTrue(fa["coupled_core_rational_barrier_verified"])

        fb = audit_w6_front_b_zero_diag_block_return_and_cousin_diamond3()
        self.assertTrue(fb["zero_diag_r1_sub6_barrier_verified"])
        self.assertTrue(fb["spiral_r_block_unbounded_climb_verified"])
        self.assertTrue(fb["spiral_mod4_eq1_matches_syracuse_verified"])
        self.assertTrue(fb["cousin_diamond3_outside_cone4_descent_verified"])
        self.assertTrue(fb["cousin_diamond3_phi2_jump_at_169_verified"])
        self.assertTrue(fb["cousin_diamond3_cone4_exact_return_verified"])
        self.assertTrue(fb["cousin_diamond3_matches_4_laurent_families_verified"])
        self.assertTrue(fb["cousin_diamond3_countermodels_verified"])

        fc = audit_w6_front_c_laurent_determinants_and_2block_locks()
        self.assertTrue(fc["laurent_det_dip_explosion_and_scaling_verified"])
        self.assertTrue(fc["laurent_resonant_divisibility_verified"])
        self.assertTrue(fc["twoblock_equal_even_lock_and_cone_exclusion_verified"])

        fd = audit_w6_front_d_cross_ray_disjointness_and_prefix_covering()
        self.assertTrue(fd["q0_loop_collision_sharp_at_184111_verified"])
        self.assertTrue(fd["q_pos_cross_ray_disjointness_verified"])
        self.assertTrue(fd["mod512_prefix_partition_11_plus_16_eq_27_verified"])
        self.assertTrue(fd["mod512_uniform_fibers_L10_to_L12_verified"])
        self.assertTrue(fd["exponential_q_sparsity_and_bounded_noncovering_verified"])

    def test_wave6_boundary_guards_synthetic_predicates_and_ground_truth_corruption(self) -> None:
        import json
        import tempfile
        from collatz_analysis.cs_cegar_redteam import (
            _dynamic_pred_coupled_core_preimage_syracuse,
            _dynamic_pred_fixed_grid_laurent_extrapolation,
            _dynamic_pred_phi2_on_cousin_diamond3,
            _dynamic_pred_q0_ray_injectivity_without_first_hit,
            _dynamic_pred_spiral_2block_monotone,
            _solve_laurent_2log_interpolation_det,
            cousin_diamond2_phi,
            cousin_diamond3_block_return,
            cousin_diamond3_step_int,
            cousin_diamond3_step_q6,
            default_witness_bank_path,
            evaluate_hypothesis_against_witness_bank,
            is_diamond3_cone4,
            spiral_block_return_int,
            verify_witness_bank_ground_truth,
        )

        # 1. Explicit boundary & error-path ValueError guards (including bool-as-int rejection)
        for bad_bool in (False, True):
            with self.assertRaises(ValueError):
                is_diamond3_cone4(bad_bool)
            with self.assertRaises(ValueError):
                cousin_diamond3_step_int(bad_bool)
            with self.assertRaises(ValueError):
                cousin_diamond3_step_int(7, q=bad_bool)
            with self.assertRaises(ValueError):
                cousin_diamond3_step_q6(bad_bool)  # type: ignore[arg-type]
            with self.assertRaises(ValueError):
                cousin_diamond3_block_return(bad_bool)
            with self.assertRaises(ValueError):
                spiral_block_return_int(bad_bool)
            with self.assertRaises(ValueError):
                _solve_laurent_2log_interpolation_det(bad_bool, 8, 2, 2, 2, 2)
        for bad_q in (0, -3, 2, 4):
            with self.assertRaises(ValueError):
                cousin_diamond3_step_int(7, q=bad_q)
        for bad_frac in (Fraction(1, 2), Fraction(1, 3), Fraction(5, 6)):
            with self.assertRaises(ValueError):
                cousin_diamond3_step_q6(bad_frac)
        for bad_x in (0, -1, -5):
            with self.assertRaises(ValueError):
                cousin_diamond3_block_return(bad_x)
        for bad_odd in (0, -1, -3, 2, 4, 18):
            with self.assertRaises(ValueError):
                spiral_block_return_int(bad_odd)
        with self.assertRaises(ValueError):
            _solve_laurent_2log_interpolation_det(0, 8, 2, 2, 2, 2)
        with self.assertRaises(ValueError):
            _solve_laurent_2log_interpolation_det(5, 0, 2, 2, 2, 2)
        with self.assertRaises(ValueError):
            _solve_laurent_2log_interpolation_det(5, 8, 0, 2, 2, 2)
        with self.assertRaises(ValueError):
            _solve_laurent_2log_interpolation_det(5, 8, 3, 3, 4, 2)
        with self.assertRaises(ValueError):
            _solve_laurent_2log_interpolation_det(5, 8, 2, 2, 2, 2, prec=20)

        # 2. Boundary & threshold checks (x = 41 < 169 vs x = 169, x = 2 vs x = 20, U = 1 resonant collapse)
        self.assertFalse(is_diamond3_cone4(41))  # 3*41 + 5 = 128 = 2^7, but x < 169
        self.assertTrue(is_diamond3_cone4(169))  # 3*169 + 5 = 512 = 2^9
        self.assertEqual(cousin_diamond3_step_int(0), 0)
        self.assertEqual(cousin_diamond3_step_int(1), 2)
        self.assertEqual(cousin_diamond3_step_int(2), 1)
        self.assertEqual(cousin_diamond3_step_int(20), 2)
        self.assertEqual(cousin_diamond3_step_q6(Fraction(20, 1)), Fraction(2, 1))
        self.assertEqual(cousin_diamond3_block_return(1), (0, 1))
        self.assertEqual(cousin_diamond3_block_return(2), (1, 1))
        self.assertEqual(cousin_diamond3_block_return(169), (13, 1))
        self.assertEqual(spiral_block_return_int(1), 1)
        self.assertEqual(spiral_block_return_int(1019), 1147)
        self.assertEqual(spiral_block_return_int(1147), 1291)
        big = (1 << 260) - 1
        self.assertFalse(is_diamond3_cone4(big))
        self.assertLess(cousin_diamond2_phi(cousin_diamond3_step_int(big)), cousin_diamond2_phi(big))

        # U = 1 (u = 0) resonant determinant collapse at (W=1, K=1, R=2, S=2, T=4, U=1) & (3, 5, 6, 4, 24, 1)
        det_u1_res = _solve_laurent_2log_interpolation_det(1, 1, 2, 2, 4, 1)
        self.assertEqual(det_u1_res["det_int"], 0)
        self.assertFalse(det_u1_res["det_nonzero"])
        self.assertEqual(det_u1_res["homog_formula_diff"], 0.0)
        det_u1_35 = _solve_laurent_2log_interpolation_det(3, 5, 6, 4, 24, 1)
        self.assertEqual(det_u1_35["det_int"], 0)
        self.assertFalse(det_u1_35["det_nonzero"])
        self.assertEqual(det_u1_35["homog_formula_diff"], 0.0)
        det_4x4_58 = _solve_laurent_2log_interpolation_det(5, 8, 2, 2, 2, 2)
        self.assertEqual(det_4x4_58["det_int"], 8)
        self.assertTrue(det_4x4_58["det_nonzero"])
        det_4x4_mod_only = _solve_laurent_2log_interpolation_det(5, 8, 2, 2, 2, 2, exact_int=False)
        self.assertIsNone(det_4x4_mod_only["det_int"])
        self.assertTrue(det_4x4_mod_only["det_nonzero"])
        det_306_scaled = _solve_laurent_2log_interpolation_det(306, 485, 10, 10, 20, 5)
        self.assertIsNone(det_306_scaled["det_int"])
        self.assertTrue(det_306_scaled["det_nonzero"])
        self.assertLess(det_306_scaled["det_m0_log2"], -660.0)
        self.assertLess(det_306_scaled["homog_formula_diff"], 1e-8)

        # Ledger sync & load_witness_bank metadata validation
        from collatz_analysis.cs_cegar_redteam import load_witness_bank

        pkg_dir_local = Path(__file__).resolve().parent.parent
        ledger_txt = (pkg_dir_local / "PROOF_SPACE_LEDGER.md").read_text(encoding="utf-8")
        live_bank = load_witness_bank()
        by_hid = {rec["hypothesis_id"]: rec for rec in live_bank["falsified_hypotheses"]}
        self.assertEqual(
            by_hid["W6_H2B_SPIRAL_BLOCK_RETURN_LAURENT_AND_MONOTONE_RANKINGS"]["branch"],
            "P5.5",
        )
        for rec in live_bank["falsified_hypotheses"]:
            br = rec["branch"]
            if "." in br:
                self.assertIn(f"| `{br}` |", ledger_txt)
            else:
                self.assertIn(f"Branch {br}", ledger_txt)

        # 3. Dynamic predicates catch brand-new synthetic witness IDs without hardcoded ID lookup
        with tempfile.TemporaryDirectory() as tmpdir:
            fresh_bank = Path(tmpdir) / "fresh_w6_bank.json"
            base = json.loads(default_witness_bank_path().read_text(encoding="utf-8"))
            base["falsified_hypotheses"] = []
            base["domains"]["z_pos_high_glide"] = [
                {"witness_id": "SYNTH_MERSENNE_7", "seed": 7, "kills_mechanisms": ["test"]},
                {"witness_id": "SYNTH_CONE4_681", "seed": 681, "kills_mechanisms": ["test"]},
                {"witness_id": "SYNTH_SPIRAL_1019", "seed": 1019, "kills_mechanisms": ["test"]},
                {
                    "witness_id": "SYNTH_LOOP_5",
                    "seed": 5,
                    "core_word": [1],
                    "loop_core_word": [1, 0, 1],
                    "kills_mechanisms": ["test"],
                },
            ]
            base["domains"]["log2_3_convergents"] = [
                {
                    "witness_id": "SYNTH_LAURENT_GRID",
                    "laurent_grid": [6, 6, 12, 3],
                    "low_W": 12,
                    "low_K": 19,
                    "high_W": 41,
                    "high_K": 65,
                    "kills_mechanisms": ["test"],
                }
            ]
            fresh_bank.write_text(json.dumps(base), encoding="utf-8")

            r_cc = evaluate_hypothesis_against_witness_bank(
                "SynthCC", _dynamic_pred_coupled_core_preimage_syracuse, ("z_pos_high_glide",), fresh_bank
            )
            self.assertEqual(r_cc["minimal_failure"], ("z_pos_high_glide", "SYNTH_MERSENNE_7"))

            r_d3 = evaluate_hypothesis_against_witness_bank(
                "SynthD3", _dynamic_pred_phi2_on_cousin_diamond3, ("z_pos_high_glide",), fresh_bank
            )
            self.assertEqual(r_d3["minimal_failure"], ("z_pos_high_glide", "SYNTH_CONE4_681"))

            r_sp = evaluate_hypothesis_against_witness_bank(
                "SynthSp", _dynamic_pred_spiral_2block_monotone, ("z_pos_high_glide",), fresh_bank
            )
            self.assertEqual(r_sp["minimal_failure"], ("z_pos_high_glide", "SYNTH_SPIRAL_1019"))

            r_q0 = evaluate_hypothesis_against_witness_bank(
                "SynthQ0", _dynamic_pred_q0_ray_injectivity_without_first_hit, ("z_pos_high_glide",), fresh_bank
            )
            self.assertEqual(r_q0["minimal_failure"], ("z_pos_high_glide", "SYNTH_LOOP_5"))

            r_lg = evaluate_hypothesis_against_witness_bank(
                "SynthLG", _dynamic_pred_fixed_grid_laurent_extrapolation, ("log2_3_convergents",), fresh_bank
            )
            self.assertEqual(r_lg["minimal_failure"], ("log2_3_convergents", "SYNTH_LAURENT_GRID"))

            # 4. Corrupting each Wave 6 ground-truth schema field fails verify_witness_bank_ground_truth
            corrupt = json.loads(default_witness_bank_path().read_text(encoding="utf-8"))
            for e in corrupt["domains"]["z_pos_high_glide"]:
                if e["witness_id"] == "ZPOS_SPINE_DYADIC_JUMP_169_TO_127":
                    e["cousin_diamond3_steps_to_1"] = 999
                elif e["witness_id"] == "ZPOS_SPIRAL_2BLOCK_1019_CLIMB":
                    e["spiral_block_2_next"] = 999
                elif e["witness_id"] == "ZPOS_RAY_Q0_LOOP_COLLISION_184111":
                    e["loop_core_word"] = [1, 1]
            for e in corrupt["domains"]["m1_q2_pos"]:
                if e["witness_id"] == "M1_COUSIN_DIAMOND3_1_OVER_7":
                    e["orbit"][1] = "99/7"
            for e in corrupt["domains"]["m3_supercritical"]:
                if e["witness_id"] == "M3_COUSIN_DIAMOND3_7X1_CYCLE5":
                    e["orbit"][1] = 999
            for e in corrupt["domains"]["log2_3_convergents"]:
                if e["witness_id"] == "LAURENT_DET_6X6_12X3_W12_DIP_AND_W41_EXPLOSION":
                    e["high_det_m0_log2"] = -999.0
            corrupt_path = Path(tmpdir) / "corrupt_w6.json"
            corrupt_path.write_text(json.dumps(corrupt), encoding="utf-8")
            gt_bad = verify_witness_bank_ground_truth(corrupt_path)
            self.assertFalse(gt_bad["all_witnesses_ground_truth_verified"])
            for expected_id in (
                "ZPOS_SPINE_DYADIC_JUMP_169_TO_127",
                "ZPOS_SPIRAL_2BLOCK_1019_CLIMB",
                "ZPOS_RAY_Q0_LOOP_COLLISION_184111",
                "M1_COUSIN_DIAMOND3_1_OVER_7",
                "M3_COUSIN_DIAMOND3_7X1_CYCLE5",
                "LAURENT_DET_6X6_12X3_W12_DIP_AND_W41_EXPLOSION",
            ):
                self.assertIn(expected_id, gt_bad["failed_witness_ids"])

            # 5. Schema validation rejects invalid status, invalid branch, or blank kills_mechanisms
            for mut_kind in ("bad_status", "bad_branch", "blank_kill"):
                bad_schema = json.loads(default_witness_bank_path().read_text(encoding="utf-8"))
                if mut_kind == "bad_status":
                    bad_schema["falsified_hypotheses"][-1]["status"] = "OPEN"
                elif mut_kind == "bad_branch":
                    bad_schema["falsified_hypotheses"][-1]["branch"] = "P9.1"
                else:
                    bad_schema["domains"]["z_pos_high_glide"][0]["kills_mechanisms"] = ["   "]
                bad_p = Path(tmpdir) / f"{mut_kind}.json"
                bad_p.write_text(json.dumps(bad_schema), encoding="utf-8")
                with self.assertRaises(ValueError):
                    load_witness_bank(bad_p)

    def test_wave6_lean4_zero_custom_axioms_and_docstring_audit(self) -> None:
        import re
        from collatz_analysis.formal_proofs import (
            ALLOWED_LEAN4_FOUNDATIONAL_AXIOMS,
            verify_lean4_kernel_proofs,
        )

        pkg_dir = Path(__file__).resolve().parent.parent
        res = verify_lean4_kernel_proofs()
        self.assertTrue(res["pure_kernel_verified"])
        self.assertEqual(len(res["lean_files"]), 55)
        self.assertGreaterEqual(res["theorems_audited"], 1593)
        self.assertGreaterEqual(res["axiom_free_theorem_count"], 550)
        self.assertTrue(any(Path(p).name == "Wave6WholeSpace.lean" for p in res["lean_files"]))

        ax_map = res["axioms_by_theorem"]
        w6_theorems = (
            "coupled_core_weight_survives_spine_and_17_yet_fails_mersenne",
            "spine_bounded_ratio_preimage_impossibility",
            "berg_meinardus_coupled_core_rational_weight_impossibility",
            "sub6_upper_tri_2d_forces_zero_diag_B0",
            "zero_diag_upper_tri_2d_r1_sub6_impossibility",
            "zero_top_left_breaks_left_context_monotonicity_2d",
            "bipartite_zero_diag_swap_r1_impossibility_all_dim",
            "antidiag_swap_2d_r1_impossibility",
            "spiral_block_return_unbounded_climb",
            "three_family_multiterm_laurent_obstruction",
            "spiral_block_return_multiterm_laurent_impossibility",
            "cousinDiamond3StepInt_ofNat_eq",
            "cousin_diamond3_outside_cone4_strict_descent",
            "pow9_succ_add_seven_ne_pow2",
            "cousin_diamond3_cone4_reaches_one_exact",
            "cousin_diamond3_global_convergence",
            "cousin_diamond3_multiterm_laurent_impossibility",
            "cousin_diamond3_counter_model_separation",
            "laurent_interp_2x2_5_8_and_3x3_determinant_cert",
            "laurent_interp_resonant_row_collapse_and_gap_divisibility",
            "m_block_antipodal_shared_mersenne_parity_and_mod3_lock",
            "two_block_shared_mersenne_propagation_and_equal_even_exclusion",
            "first_hit_ray_global_disjointness_and_q0_necessity",
            "mod512_surviving_prefix_partition_cert",
            "exactBackwardQuotient_mod512_eq_coreWordMod512",
            "mod512_surviving_prefix_uniform_fibers",
            "survivingMod512Bool_nine_prefix_head_two_true_grid",
            "surviving_mod512_nine_prefix_auto_weight_and_characterization",
            "bounded_length_ray_exponential_sparsity_and_noncovering",
            "bounded_length_ray_logarithmic_counting_zero_density",
        )
        for thm in w6_theorems:
            self.assertIn(thm, ax_map)
            self.assertTrue(
                set(ax_map[thm]).issubset(ALLOWED_LEAN4_FOUNDATIONAL_AXIOMS),
                f"Unexpected custom axiom in {thm}: {ax_map[thm]}",
            )

        self.assertEqual(ax_map["cousin_diamond3_counter_model_separation"], [])
        self.assertEqual(ax_map["laurent_interp_2x2_5_8_and_3x3_determinant_cert"], [])
        self.assertEqual(ax_map["survivingMod512Bool_nine_prefix_head_two_true_grid"], [])
        for choice_free_thm in (
            "zero_top_left_breaks_left_context_monotonicity_2d",
            "mod512_surviving_prefix_partition_cert",
            "laurent_interp_resonant_row_collapse_and_gap_divisibility",
            "pow9_succ_add_seven_ne_pow2",
        ):
            self.assertNotIn("Classical.choice", ax_map[choice_free_thm])

        w6_src = (pkg_dir / "CollatzFormal/Wave6WholeSpace.lean").read_text(encoding="utf-8")
        for doc, thm_name in re.findall(r"/--\s*(.*?)\s*-/\s*theorem\s+([A-Za-z0-9_']+)\b", w6_src, flags=re.S):
            if "`[]` axioms" in doc:
                self.assertEqual(ax_map.get(thm_name), [], f"False []-axiom docstring on {thm_name}")
            if "choice-free" in doc:
                self.assertNotIn("Classical.choice", ax_map.get(thm_name, []), f"False choice-free docstring on {thm_name}")
        for thm_ref in re.findall(r"`([A-Za-z0-9_']+)`\s*\(`\[\]`\s*axioms\)", w6_src, flags=re.I):
            self.assertEqual(ax_map.get(thm_ref), [], f"False []-axiom header/comment claim on {thm_ref}")
        self.assertNotIn("(`[]` Axioms)", w6_src)

    def test_cli_summary_includes_wave6_loop_and_exit_gate(self) -> None:
        import contextlib
        import io
        from unittest import mock
        from collatz_analysis.cli import main as cli_main

        buf_sum = io.StringIO()
        with contextlib.redirect_stdout(buf_sum):
            rc_sum = cli_main(["--summary", "--dp-depth", "50"])
        self.assertEqual(rc_sum, 0)
        out = buf_sum.getvalue()
        self.assertIn("[Wave 6 Whole-Space Proof Loop]", out)
        self.assertIn("A=True (deg-surv=0), zero-diag/spiral=True, T_diamond3=True", out)
        self.assertIn("Laurent=True, 2-blk-lock=True, rays/11+16/sparse=True", out)
        self.assertLess(
            out.index("[Wave 5 Whole-Space Proof Loop]"),
            out.index("[Wave 6 Whole-Space Proof Loop]"),
        )
        self.assertLess(
            out.index("[Wave 6 Whole-Space Proof Loop]"),
            out.index("[Lean 4 Kernel Verification]"),
        )

        failed_w6 = {
            "passed": False,
            "verdict": "FALSIFIED",
            "universality_gate_passed": True,
            "witness_bank_total_entries": 47,
            "witness_bank_falsified_count": 16,
            "witness_bank_ground_truth_verified": True,
            "front_a_coupled_core_preimage": {
                "coupled_core_rational_barrier_verified": True,
                "effective_degree_cone_survivors": 0,
            },
            "front_b_zero_diag_spiral_and_diamond3": {
                "zero_diag_r1_sub6_barrier_verified": True,
                "spiral_r_block_unbounded_climb_verified": True,
                "cousin_diamond3_outside_cone4_descent_verified": False,
                "cousin_diamond3_cone4_exact_return_verified": True,
                "cousin_diamond3_matches_4_laurent_families_verified": True,
                "cousin_diamond3_countermodels_verified": True,
            },
            "front_c_laurent_and_2block_locks": {
                "laurent_det_dip_explosion_and_scaling_verified": False,
                "laurent_resonant_divisibility_verified": True,
                "twoblock_equal_even_lock_and_cone_exclusion_verified": True,
            },
            "front_d_cross_ray_and_prefix_covering": {
                "q_pos_cross_ray_disjointness_verified": True,
                "mod512_prefix_partition_11_plus_16_eq_27_verified": True,
                "mod512_uniform_fibers_L10_to_L12_verified": True,
                "exponential_q_sparsity_and_bounded_noncovering_verified": True,
            },
        }
        buf_fail = io.StringIO()
        with mock.patch(
            "collatz_analysis.cs_cegar_redteam.run_wave6_whole_space_campaign",
            return_value=failed_w6,
        ), mock.patch(
            "collatz_analysis.cli.verify_lean4_kernel_proofs",
            return_value={"lean_available": False, "static_hygiene_clean": True},
        ), contextlib.redirect_stdout(buf_fail):
            rc_fail = cli_main(["--summary", "--dp-depth", "10"])
        self.assertEqual(rc_fail, 1)
        self.assertIn("T_diamond3=False", buf_fail.getvalue())
        self.assertIn("Laurent=False", buf_fail.getvalue())


if __name__ == "__main__":
    unittest.main()
