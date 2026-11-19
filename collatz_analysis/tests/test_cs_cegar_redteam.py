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
        self.assertGreaterEqual(len(bank["domains"]["z_pos_high_glide"]), 17)

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
        self.assertGreaterEqual(len(res["lean_files"]), 55)
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


class TestWave7WholeSpaceCampaign(unittest.TestCase):
    """Deep unit, edge-case, corruption, and Lean 4 kernel tests for Wave 7."""

    def test_wave7_exports_witness_bank_and_all_four_fronts(self) -> None:
        import collatz_analysis as ca
        from collatz_analysis.cs_cegar_redteam import (
            audit_w7_front_a_laurent_bridge_and_common_order_primes,
            audit_w7_front_b_binary_digit_weights_and_mahler_tauberian,
            audit_w7_front_c_hofbauer_waldmann_3d_vass_and_diamond4,
            audit_w7_front_d_markov_shift_q0_envelope_and_l2_dispersion,
            load_witness_bank,
            run_wave7_whole_space_campaign,
            verify_witness_bank_ground_truth,
        )

        for exported_sym in (
            "binary_popcount",
            "binary_one_runs",
            "binary_alt_transitions",
            "binary_digit_signature6",
            "is_diamond4_cone5",
            "cousin_diamond4_step_int",
            "cousin_diamond4_step_q6",
            "cousin_diamond4_block_return",
            "audit_w7_front_a_laurent_bridge_and_common_order_primes",
            "audit_w7_front_b_binary_digit_weights_and_mahler_tauberian",
            "audit_w7_front_c_hofbauer_waldmann_3d_vass_and_diamond4",
            "audit_w7_front_d_markov_shift_q0_envelope_and_l2_dispersion",
            "run_wave7_whole_space_campaign",
        ):
            self.assertTrue(hasattr(ca, exported_sym), f"Missing package export: {exported_sym}")

        bank = load_witness_bank()
        self.assertGreaterEqual(len(bank["domains"]["z_pos_high_glide"]), 20)
        self.assertGreaterEqual(sum(len(v) for v in bank["domains"].values()), 53)
        self.assertGreaterEqual(len(bank["falsified_hypotheses"]), 20)

        truth = verify_witness_bank_ground_truth()
        self.assertTrue(truth["all_witnesses_ground_truth_verified"])
        self.assertGreaterEqual(truth["verified_witness_count"], 53)
        self.assertEqual(truth["failed_witness_ids"], ())

        w7 = run_wave7_whole_space_campaign()
        self.assertTrue(w7["passed"])
        self.assertEqual(w7["verdict"], "REDTEAM-PASSED")
        self.assertTrue(w7["universality_gate_passed"])
        self.assertGreaterEqual(w7["witness_bank_total_entries"], 53)
        self.assertGreaterEqual(w7["witness_bank_falsified_count"], 20)

        fa = audit_w7_front_a_laurent_bridge_and_common_order_primes()
        self.assertTrue(fa["moderate_w41_cofactor_stripping_verified"])
        self.assertTrue(fa["wdilated_zero_gap_congruence_and_2x2_verified"])
        self.assertTrue(fa["one_block_common_divisor_impossible_verified"])
        self.assertEqual(fa["odd_primes_lt_300_count"], 60)
        self.assertEqual(fa["excluded_1block_primes_lt_300_count"], 60)
        self.assertTrue(fa["all_60_primes_lt_300_excluded_1block"])
        self.assertEqual(fa["coprime_order_primes_lt_6000"], (331,))
        self.assertTrue(fa["unique_coprime_prime_331_verified"])
        self.assertTrue(fa["twoblock_order_ge5_primes_verified"])
        self.assertTrue(fa["twoblock_odd_order_primes_41r_verified"])

        fb = audit_w7_front_b_binary_digit_weights_and_mahler_tauberian()
        self.assertTrue(fb["binary_digit_and_bitlength_family_verified"])
        self.assertTrue(fb["popcount_3_cancellation_on_11_and_200_verified"])
        self.assertEqual(fb["exponential_digit_entropy_survivors"], 0)
        self.assertTrue(fb["mahler_koopman_balance_and_m3_nonuniqueness_verified"])

        fc = audit_w7_front_c_hofbauer_waldmann_3d_vass_and_diamond4()
        self.assertTrue(fc["r1_sub6_2d_nontriangular_hw_cert_verified"])
        self.assertTrue(fc["r1_sub6_3d_nontriangular_hw_cert_verified"])
        self.assertTrue(fc["parikh_vass_impossibility_verified"])
        self.assertTrue(fc["lower_tri_and_omega_k_stall_verified"])
        self.assertTrue(fc["cousin_diamond4_r_block_spiral_climb_verified"])
        self.assertTrue(fc["cousin_diamond4_outside_cones45_descent_verified"])
        self.assertTrue(fc["cousin_diamond4_cone5_exact_return_verified"])
        self.assertTrue(fc["cousin_diamond4_countermodels_verified"])

        fd = audit_w7_front_d_markov_shift_q0_envelope_and_l2_dispersion()
        self.assertTrue(fd["markov_suffix_shift_recurrence_and_oddness_verified"])
        self.assertTrue(fd["q0_archimedean_two_sided_envelope_verified"])
        self.assertTrue(fd["fixed_length_injectivity_and_minimal_l2_energy_verified"])
        self.assertTrue(fd["nonmonotone_l12_below_l10_min_leaf_verified"])

    def test_wave7_edge_cases_error_paths_and_witness_corruption(self) -> None:
        import copy
        from fractions import Fraction
        import json
        import tempfile
        from collatz_analysis.cs_cegar_redteam import (
            _dynamic_pred_all_odd_primes_have_common_order_ge2,
            _dynamic_pred_binary_digit_sig_distinguishes_preimages,
            _dynamic_pred_moderate_w_laurent_kills_cubic_gap,
            _dynamic_pred_phi2_on_cousin_diamond4_cone5,
            _dynamic_pred_q0_min_leaf_monotone_in_core_length,
            _mult_order_mod_prime,
            _solve_laurent_perturbed_cubic_gap_det,
            binary_alt_transitions,
            binary_digit_signature6,
            binary_one_runs,
            binary_popcount,
            cousin_diamond4_block_return,
            cousin_diamond4_step_int,
            cousin_diamond4_step_q6,
            evaluate_hypothesis_against_witness_bank,
            is_diamond4_cone5,
            load_witness_bank,
            verify_witness_bank_ground_truth,
        )

        # Boundary values 0, 1, 2 for binary digit primitives
        self.assertEqual(binary_popcount(0), 0)
        self.assertEqual(binary_one_runs(0), 0)
        self.assertEqual(binary_alt_transitions(0), 0)
        self.assertEqual(binary_alt_transitions(1), 0)
        self.assertEqual(binary_digit_signature6(0), (0, 0, 0, 1, 1, 0))
        self.assertEqual(binary_digit_signature6(200), (3, 2, 3, 4, 3, 4))
        self.assertEqual(binary_digit_signature6(400), (3, 2, 3, 4, 3, 4))
        self.assertEqual(binary_digit_signature6(133), (3, 3, 4, 3, 2, 3))

        for bad in (-1, True, False, 1.5, "10"):
            for fn in (binary_popcount, binary_one_runs, binary_alt_transitions, binary_digit_signature6):
                with self.assertRaises(ValueError):
                    fn(bad)  # type: ignore[arg-type]

        # Threshold & error checks for T_diamond4 and Cone 5
        self.assertFalse(is_diamond4_cone5(25))  # 25 % 32 == 25 and 25 % 3 != 2, < 89
        self.assertFalse(is_diamond4_cone5(57))  # 57 < 89
        self.assertTrue(is_diamond4_cone5(89))   # 32 * 3 - 7 = 89 (minimal Cone 5 member)
        self.assertEqual(cousin_diamond4_step_int(89), 67)
        self.assertEqual(cousin_diamond4_step_int(1019), 1529)
        self.assertEqual(cousin_diamond4_step_int(1529), 1147)
        self.assertEqual(cousin_diamond4_step_int(1147), 1721)
        self.assertEqual(cousin_diamond4_step_int(1721), 1291)
        self.assertEqual(cousin_diamond4_block_return(1), (0, 1))
        self.assertEqual(cousin_diamond4_block_return(2), (1, 1))
        self.assertEqual(cousin_diamond4_block_return(169), (13, 1))   # Cone 4
        self.assertEqual(cousin_diamond4_block_return(1529), (13, 1))  # Cone 5 (a0=3)
        self.assertEqual(cousin_diamond4_block_return(89), (8, 1))     # Cone 5 (a0=2)

        for bad_x in (True, False, 2.5, "89"):
            with self.assertRaises(ValueError):
                is_diamond4_cone5(bad_x)  # type: ignore[arg-type]
            with self.assertRaises(ValueError):
                cousin_diamond4_step_int(bad_x)  # type: ignore[arg-type]
            with self.assertRaises(ValueError):
                cousin_diamond4_step_q6(bad_x)  # type: ignore[arg-type]
        for bad_q in (1, 2, 4, -3, True):
            with self.assertRaises(ValueError):
                cousin_diamond4_step_int(7, q=bad_q)  # type: ignore[arg-type]
        for bad_pos in (0, -1, True):
            with self.assertRaises(ValueError):
                cousin_diamond4_block_return(bad_pos)  # type: ignore[arg-type]
        for bad_frac in (Fraction(1, 2), Fraction(1, 3), Fraction(5, 6)):
            with self.assertRaises(ValueError):
                cousin_diamond4_step_q6(bad_frac)

        # Error checks for _mult_order_mod_prime and _solve_laurent_perturbed_cubic_gap_det
        self.assertEqual(_mult_order_mod_prime(2, 331), 30)
        self.assertEqual(_mult_order_mod_prime((3 * pow(2, -1, 331)) % 331, 331), 11)
        for bad_args in ((2, 2), (2, 1), (7, 7), (True, 5), (2, False)):
            with self.assertRaises(ValueError):
                _mult_order_mod_prime(*bad_args)  # type: ignore[arg-type]
        with self.assertRaises(ValueError):
            _solve_laurent_perturbed_cubic_gap_det(5, 8, 2, 2, 3, 1)  # R*S != T*U

        # Synthetic witness-bank check on all 5 Wave 7 dynamic predicates (proving zero hardcoded IDs)
        base_bank = load_witness_bank()
        with tempfile.TemporaryDirectory() as tmpdir:
            synth_bank = copy.deepcopy(base_bank)
            synth_bank["falsified_hypotheses"] = []
            synth_bank["domains"]["z_pos_high_glide"] = [
                {
                    "witness_id": "SYNTH_DIGIT_3080",
                    "seed": 2053,
                    "next_compressed": 3080,  # m_5 = 3 * 4^5 + 8
                    "even_sibling": 6160,
                    "kills_mechanisms": ["binary_digit_sig"],
                },
                {
                    "witness_id": "SYNTH_D4_CONE5_185",
                    "seed": 185,  # 2^6 * 3 - 7 -> 139 (Phi_2 jumps 60446 -> 172524)
                    "kills_mechanisms": ["phi2_on_diamond4"],
                },
                {
                    "witness_id": "SYNTH_RAY_DROP",
                    "seed": 9474989262494029914559180158261332877999850457196839609824416569371275282207997551,
                    "core_word": [1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1],
                    "shorter_l10_min_core_word": [1, 1, 1, 1, 1, 0, 1, 1, 0, 1],
                    "kills_mechanisms": ["q0_monotone_len"],
                },
            ]
            synth_bank["domains"]["log2_3_convergents"] = [
                {
                    "witness_id": "SYNTH_LAURENT_AND_331",
                    "W": 41,
                    "K": 65,
                    "laurent_scaled_grid": [8, 8, 16, 4],
                    "coprime_order_barrier_prime": 331,
                    "kills_mechanisms": ["moderate_w_laurent", "all_prime_gcd"],
                }
            ]
            synth_p = Path(tmpdir) / "synth_w7.json"
            synth_p.write_text(json.dumps(synth_bank), encoding="utf-8")

            r1 = evaluate_hypothesis_against_witness_bank(
                "SynthDigit", _dynamic_pred_binary_digit_sig_distinguishes_preimages,
                domains=("z_pos_high_glide",), bank_path=synth_p,
            )
            self.assertEqual(r1["minimal_failure"], ("z_pos_high_glide", "SYNTH_DIGIT_3080"))
            r2 = evaluate_hypothesis_against_witness_bank(
                "SynthD4", _dynamic_pred_phi2_on_cousin_diamond4_cone5,
                domains=("z_pos_high_glide",), bank_path=synth_p,
            )
            self.assertEqual(r2["minimal_failure"], ("z_pos_high_glide", "SYNTH_D4_CONE5_185"))
            r3 = evaluate_hypothesis_against_witness_bank(
                "SynthLaurent", _dynamic_pred_moderate_w_laurent_kills_cubic_gap,
                domains=("log2_3_convergents",), bank_path=synth_p,
            )
            self.assertEqual(r3["minimal_failure"], ("log2_3_convergents", "SYNTH_LAURENT_AND_331"))
            r4 = evaluate_hypothesis_against_witness_bank(
                "SynthPrime", _dynamic_pred_all_odd_primes_have_common_order_ge2,
                domains=("log2_3_convergents",), bank_path=synth_p,
            )
            self.assertEqual(r4["minimal_failure"], ("log2_3_convergents", "SYNTH_LAURENT_AND_331"))
            r5 = evaluate_hypothesis_against_witness_bank(
                "SynthRay", _dynamic_pred_q0_min_leaf_monotone_in_core_length,
                domains=("z_pos_high_glide",), bank_path=synth_p,
            )
            self.assertEqual(r5["minimal_failure"], ("z_pos_high_glide", "SYNTH_RAY_DROP"))

            # Verify ground-truth corruption detection across all 6 new Wave 7 witnesses
            corruptions = [
                ("z_pos_high_glide", "ZPOS_BINARY_RUN_COLLISION_200", "digit_sig_target", [3, 2, 3, 4, 3, 5]),
                ("z_pos_high_glide", "ZPOS_COUSIN_DIAMOND4_CONE5_1529_JUMP", "cousin_diamond4_steps_to_1", 12),
                ("z_pos_high_glide", "ZPOS_RAY_Q0_NONMONOTONE_LENGTH_DROP_L12", "compressed_steps_to_1", 284),
                ("m1_q2_pos", "M1_COUSIN_DIAMOND4_1_OVER_7", "orbit", ["1/7", "5/7", "11/7", "20/7", "3/7"]),
                ("m3_supercritical", "M3_COUSIN_DIAMOND4_7X1_CYCLE5", "orbit", [5, 18, 9, 32, 11]),
                ("log2_3_convergents", "LAURENT_SCALED_W41_CUBIC_GAP_AND_PRIME331_BARRIER", "ord2_mod_p", 15),
            ]
            bad_b = copy.deepcopy(base_bank)
            for dom, wid, field, bad_val in corruptions:
                for item in bad_b["domains"][dom]:
                    if item["witness_id"] == wid:
                        item[field] = bad_val
            bad_p = Path(tmpdir) / "corrupt_w7_all6.json"
            bad_p.write_text(json.dumps(bad_b), encoding="utf-8")
            chk = verify_witness_bank_ground_truth(bad_p)
            self.assertFalse(chk["all_witnesses_ground_truth_verified"])
            for _, wid, _, _ in corruptions:
                self.assertIn(wid, chk["failed_witness_ids"], f"Missed corruption on {wid}")

            # Verify subtle secondary-field corruptions on Wave 7 witnesses
            subtle_corruptions = [
                ("z_pos_high_glide", "ZPOS_BINARY_RUN_COLLISION_200", "digit_sig_seed", [3, 3, 4, 3, 2, 4]),
                ("z_pos_high_glide", "ZPOS_RAY_Q0_NONMONOTONE_LENGTH_DROP_L12", "shorter_l10_min_core_word", [1, 1, 1, 1, 1, 0, 1, 0, 0, 1]),
                ("log2_3_convergents", "LAURENT_SCALED_W41_CUBIC_GAP_AND_PRIME331_BARRIER", "ord32_mod_p", 33),
            ]
            bad_b2 = copy.deepcopy(base_bank)
            for dom, wid, field, bad_val in subtle_corruptions:
                for item in bad_b2["domains"][dom]:
                    if item["witness_id"] == wid:
                        item[field] = bad_val
            bad_p2 = Path(tmpdir) / "corrupt_w7_subtle.json"
            bad_p2.write_text(json.dumps(bad_b2), encoding="utf-8")
            chk2 = verify_witness_bank_ground_truth(bad_p2)
            self.assertFalse(chk2["all_witnesses_ground_truth_verified"])
            for _, wid, _, _ in subtle_corruptions:
                self.assertIn(wid, chk2["failed_witness_ids"], f"Missed subtle corruption on {wid}")

    def test_wave7_lean4_zero_custom_axioms_docstring_and_pii_audit(self) -> None:
        import re
        from collatz_analysis.formal_proofs import (
            ALLOWED_LEAN4_FOUNDATIONAL_AXIOMS,
            verify_lean4_kernel_proofs,
        )

        pkg_dir = Path(__file__).resolve().parent.parent
        res = verify_lean4_kernel_proofs()
        self.assertTrue(res["pure_kernel_verified"])
        self.assertTrue(res["zero_sorry_verified"])
        self.assertTrue(res["zero_warnings_verified"])
        self.assertGreaterEqual(len(res["lean_files"]), 56)
        self.assertGreaterEqual(res["theorems_audited"], 1704)
        self.assertGreaterEqual(res["axiom_free_theorem_count"], 558)
        self.assertTrue(any(Path(p).name == "Wave7WholeSpace.lean" for p in res["lean_files"]))

        ax_map = res["axioms_by_theorem"]
        w7_theorems = (
            "pow_sub_pow_mean_value_sandwich",
            "intDet_two",
            "laurent_interp_2x2_closed_form_and_nonvanishing",
            "laurent_wdilated_zero_gap_entry_and_det_congruence",
            "laurent_gap_bridge_eliminates_1_and_2_block_cycles",
            "laurent_scaled_nonvanishing_eliminates_1_and_2_block_cycles",
            "one_block_common_divisor_impossibility",
            "one_block_common_order_prime_exclusion",
            "odd_order_primes_and_331_mult_order_cert",
            "one_block_odd_order_primes_7_19_23_31_43_47_71_73_and_331_barrier",
            "two_block_shared_mersenne_common_order_scaling_and_squeeze",
            "squeeze69_up_to_40_cert",
            "two_block_odd_order_primes_7_19_23_31_43_47_71_73_weight_41r_floor",
            "binary_digit_sig6_and_bitlength_infinite_collision_family",
            "berg_meinardus_binary_digit_sig_impossibility",
            "berg_meinardus_exponential_popcount_bitlength_impossibility",
            "berg_meinardus_coupled_digit_sig_and_bitlength_impossibility",
            "mahler_koopman_tauberian_balance_and_m3_nonuniqueness",
            "mahler_bivariate_pole_subtraction_and_half_exponent_decay",
            "r1_sub6_admits_2d_nontriangular_hofbauer_waldmann_cert",
            "r1_sub6_admits_3d_nontriangular_hofbauer_waldmann_cert",
            "all_dim_lower_triangular_hofbauer_waldmann_impossibility",
            "omega_k_affine_rule_removal_and_parikh_vass_impossibility",
            "swap_rule_parikh_vass_impossibility",
            "cousinDiamond4StepInt_ofNat_eq",
            "cousin_diamond4_outside_cones45_strict_descent",
            "cousin_diamond4_cone4_and_cone5_exact_return",
            "cousin_diamond4_global_convergence",
            "cousin_diamond4_r_block_spiral_climb_and_laurent_impossibility",
            "cousin_diamond4_counter_model_separation",
            "canonicalSuffixShift_append_markov_recurrence",
            "q0_leaf_two_sided_archimedean_envelope_and_l12_drop",
            "fixed_length_ray_global_injectivity_and_minimal_l2_collision_energy",
        )
        for thm in w7_theorems:
            self.assertIn(thm, ax_map)
            self.assertTrue(
                set(ax_map[thm]).issubset(ALLOWED_LEAN4_FOUNDATIONAL_AXIOMS),
                f"Unexpected custom axiom in {thm}: {ax_map[thm]}",
            )

        self.assertEqual(ax_map["odd_order_primes_and_331_mult_order_cert"], [])
        self.assertEqual(ax_map["squeeze69_up_to_40_cert"], [])
        self.assertNotIn(
            "Classical.choice",
            ax_map["one_block_odd_order_primes_7_19_23_31_43_47_71_73_and_331_barrier"],
        )
        self.assertNotIn(
            "Classical.choice",
            ax_map["mahler_bivariate_pole_subtraction_and_half_exponent_decay"],
        )
        self.assertNotIn(
            "Classical.choice",
            ax_map["swap_rule_parikh_vass_impossibility"],
        )
        self.assertEqual(ax_map["r1_sub6_admits_2d_nontriangular_hofbauer_waldmann_cert"], [])
        self.assertEqual(ax_map["r1_sub6_admits_3d_nontriangular_hofbauer_waldmann_cert"], [])
        self.assertEqual(ax_map["cousin_diamond4_counter_model_separation"], [])

        w7_src = (pkg_dir / "CollatzFormal/Wave7WholeSpace.lean").read_text(encoding="utf-8")
        for doc, thm_name in re.findall(r"/--\s*(.*?)\s*-/\s*theorem\s+([A-Za-z0-9_']+)\b", w7_src, flags=re.S):
            if "`[]` axioms" in doc:
                self.assertEqual(ax_map.get(thm_name), [], f"False []-axiom docstring on {thm_name}")
            if "choice-free" in doc:
                self.assertNotIn("Classical.choice", ax_map.get(thm_name, []), f"False choice-free docstring on {thm_name}")
        for thm_ref in re.findall(r"`([A-Za-z0-9_']+)`\s*\(`\[\]`\s*axioms\)", w7_src, flags=re.I):
            self.assertEqual(ax_map.get(thm_ref), [], f"False []-axiom header/comment claim on {thm_ref}")
        self.assertNotIn("(`[]` Axioms)", w7_src)

        # Repo-wide zero-PII / machine-path hygiene scan across tracked source & docs
        forbidden_tokens = (
            "Us" + "ers" + "\\",
            "Us" + "ers/",
            "/" + "home" + "/",
            "C:" + "\\",
            "C:" + "/",
        )
        for path in sorted(pkg_dir.rglob("*")):
            if ".lake" in path.parts or "__pycache__" in path.parts or path.is_dir():
                continue
            if path.suffix in {".py", ".lean", ".md", ".json", ".c"}:
                txt = path.read_text(encoding="utf-8")
                for tok in forbidden_tokens:
                    self.assertNotIn(tok, txt, f"Forbidden path token {tok!r} in {path.name}")

    def test_cli_summary_includes_wave7_loop_and_exit_gate(self) -> None:
        import contextlib
        import io
        from unittest import mock
        from collatz_analysis.cli import main as cli_main

        buf_sum = io.StringIO()
        with contextlib.redirect_stdout(buf_sum):
            rc_sum = cli_main(["--summary", "--dp-depth", "50"])
        self.assertEqual(rc_sum, 0)
        out = buf_sum.getvalue()
        self.assertIn("[Wave 7 Whole-Space Proof Loop]", out)
        self.assertIn("A=True, B=True", out)
        self.assertIn("2D/3D-HW=True, T_diamond4=True, Markov/L2=True", out)
        self.assertLess(
            out.index("[Wave 6 Whole-Space Proof Loop]"),
            out.index("[Wave 7 Whole-Space Proof Loop]"),
        )
        self.assertLess(
            out.index("[Wave 7 Whole-Space Proof Loop]"),
            out.index("[Lean 4 Kernel Verification]"),
        )

        failed_w7 = {
            "passed": False,
            "verdict": "FALSIFIED",
            "universality_gate_passed": True,
            "witness_bank_total_entries": 53,
            "witness_bank_falsified_count": 20,
            "witness_bank_ground_truth_verified": True,
            "front_a_laurent_and_prime_orders": {
                "wdilated_zero_gap_congruence_and_2x2_verified": False,
                "all_60_primes_lt_300_excluded_1block": True,
                "unique_coprime_prime_331_verified": True,
                "twoblock_order_ge5_primes_verified": True,
            },
            "front_b_binary_digits_and_mahler": {
                "binary_digit_and_bitlength_family_verified": True,
                "exponential_digit_entropy_survivors": 0,
                "mahler_koopman_balance_and_m3_nonuniqueness_verified": True,
            },
            "front_c_hw_3d_vass_and_diamond4": {
                "r1_sub6_2d_nontriangular_hw_cert_verified": False,
                "r1_sub6_3d_nontriangular_hw_cert_verified": True,
                "cousin_diamond4_r_block_spiral_climb_verified": False,
                "cousin_diamond4_outside_cones45_descent_verified": True,
                "cousin_diamond4_cone5_exact_return_verified": True,
                "cousin_diamond4_countermodels_verified": True,
            },
            "front_d_markov_shift_and_l2_energy": {
                "markov_suffix_shift_recurrence_and_oddness_verified": True,
                "q0_archimedean_two_sided_envelope_verified": True,
                "fixed_length_injectivity_and_minimal_l2_energy_verified": True,
            },
        }
        buf_fail = io.StringIO()
        with mock.patch(
            "collatz_analysis.cs_cegar_redteam.run_wave7_whole_space_campaign",
            return_value=failed_w7,
        ), mock.patch(
            "collatz_analysis.cli.verify_lean4_kernel_proofs",
            return_value={"lean_available": False, "static_hygiene_clean": True},
        ), contextlib.redirect_stdout(buf_fail):
            rc_fail = cli_main(["--summary", "--dp-depth", "10"])
        self.assertEqual(rc_fail, 1)
        self.assertIn("A=False", buf_fail.getvalue())
        self.assertIn("2D/3D-HW=False", buf_fail.getvalue())
        self.assertIn("T_diamond4=False", buf_fail.getvalue())


class TestWave8WholeSpaceCampaign(unittest.TestCase):
    """Deep unit, edge-case, corruption, and Lean 4 kernel tests for Wave 8."""

    def test_wave8_exports_witness_bank_and_all_four_fronts(self) -> None:
        import collatz_analysis as ca
        from collatz_analysis.cs_cegar_redteam import (
            audit_w8_front_a_srs_10_of_11_towers_and_omega_k_barriers,
            audit_w8_front_b_cyclotomic_331_and_laurent_extrapolation,
            audit_w8_front_c_ripple_carry_window_kgram_and_diamond5,
            audit_w8_front_d_cross_scale_q0_collisions_and_markov_mod6,
            load_witness_bank,
            run_wave8_whole_space_campaign,
            verify_witness_bank_ground_truth,
        )

        for exported_sym in (
            "ripple_carry_3n1_stats",
            "binary_nonzero_window_list",
            "binary_zero_window_count",
            "trivial_loop_extension",
            "is_diamond5_cone6",
            "cousin_diamond5_step_int",
            "cousin_diamond5_step_q6",
            "cousin_diamond5_block_return",
            "audit_w8_front_a_srs_10_of_11_towers_and_omega_k_barriers",
            "audit_w8_front_b_cyclotomic_331_and_laurent_extrapolation",
            "audit_w8_front_c_ripple_carry_window_kgram_and_diamond5",
            "audit_w8_front_d_cross_scale_q0_collisions_and_markov_mod6",
            "run_wave8_whole_space_campaign",
        ):
            self.assertTrue(hasattr(ca, exported_sym), f"Missing package export: {exported_sym}")

        bank = load_witness_bank()
        self.assertGreaterEqual(len(bank["domains"]["z_pos_high_glide"]), 24)
        self.assertGreaterEqual(len(bank["domains"]["m1_q2_pos"]), 14)
        self.assertGreaterEqual(len(bank["domains"]["m2_z_neg"]), 4)
        self.assertGreaterEqual(len(bank["domains"]["m3_supercritical"]), 8)
        self.assertGreaterEqual(len(bank["domains"]["log2_3_convergents"]), 11)
        self.assertGreaterEqual(sum(len(v) for v in bank["domains"].values()), 61)
        self.assertGreaterEqual(len(bank["falsified_hypotheses"]), 24)

        truth = verify_witness_bank_ground_truth()
        self.assertTrue(truth["all_witnesses_ground_truth_verified"])
        self.assertGreaterEqual(truth["verified_witness_count"], 61)
        self.assertEqual(truth["failed_witness_ids"], ())

        w8 = run_wave8_whole_space_campaign()
        self.assertTrue(w8["passed"])
        self.assertEqual(w8["verdict"], "REDTEAM-PASSED")
        self.assertTrue(w8["universality_gate_passed"])
        self.assertGreaterEqual(w8["witness_bank_total_entries"], 61)
        self.assertGreaterEqual(w8["witness_bank_falsified_count"], 24)

        fa = audit_w8_front_a_srs_10_of_11_towers_and_omega_k_barriers()
        self.assertTrue(fa["omit_r2_10_of_11_single_2d_cert_verified"])
        self.assertTrue(fa["omit_r7_10_of_11_2level_2d_tower_verified"])
        self.assertTrue(fa["omit_r5_10_of_11_3level_2d_tower_verified"])
        self.assertTrue(fa["arts_giesl_1d_semantic_dp_verified"])
        self.assertTrue(fa["interior_pumping_and_omega_k_stall_verified"])

        fb = audit_w8_front_b_cyclotomic_331_and_laurent_extrapolation()
        self.assertEqual(
            fb["coprime_order_primes_to_1210483"],
            ((331, 30, 11), (1_210_483, 182, 2217)),
        )
        self.assertTrue(fb["exact_first_two_coprime_primes_verified"])
        self.assertTrue(fb["companion_factorizations_and_m1_cancellation_verified"])
        self.assertTrue(fb["twoblock_331_floor_99_159_verified"])
        self.assertTrue(fb["laurent_taylor_column_extrapolation_verified"])

        fc = audit_w8_front_c_ripple_carry_window_kgram_and_diamond5()
        self.assertTrue(fc["ripple_carry_cascade_mersenne_and_bernoulli_verified"])
        self.assertTrue(fc["sliding_window_kgram_family_verified"])
        self.assertTrue(fc["cousin_diamond5_outside_cones456_descent_verified"])
        self.assertTrue(fc["cousin_diamond5_cone6_return_and_spiral_verified"])
        self.assertTrue(fc["cousin_diamond5_countermodels_verified"])

        fd = audit_w8_front_d_cross_scale_q0_collisions_and_markov_mod6()
        self.assertGreater(fd["cross_scale_q0_collision_pairs_le9"], 0)
        self.assertTrue(fd["cross_scale_q0_biconditional_verified"])
        self.assertTrue(fd["multiscale_surviving_q0_nodup_verified"])
        self.assertTrue(fd["markov_bijection_and_mod6_lock_verified"])

    def test_wave8_edge_cases_error_paths_and_witness_corruption(self) -> None:
        import copy
        from fractions import Fraction
        import json
        import tempfile
        from collatz_analysis import cs_forest_transfer as cft
        from collatz_analysis.cs_cegar_redteam import (
            _dynamic_pred_331_unique_coprime_order_prime,
            _dynamic_pred_local_mod331_excludes_m1_1block,
            _dynamic_pred_phi2_on_cousin_diamond5_outside_cones45,
            _dynamic_pred_q0_cross_scale_only_single_loop_collides,
            _dynamic_pred_ripple_carry_penalty_monotonicity,
            _dynamic_pred_width5_sliding_window_distinguishes_preimages,
            _scan_coprime_order_primes_up_to,
            binary_nonzero_window_list,
            binary_zero_window_count,
            cousin_diamond5_block_return,
            cousin_diamond5_step_int,
            cousin_diamond5_step_q6,
            evaluate_hypothesis_against_witness_bank,
            is_diamond5_cone6,
            load_witness_bank,
            ripple_carry_3n1_stats,
            trivial_loop_extension,
            verify_witness_bank_ground_truth,
        )

        # Boundary values 0, 1, 2, 341, 682, 800, 1600
        self.assertEqual(ripple_carry_3n1_stats(0), (0, 0))
        self.assertEqual(ripple_carry_3n1_stats(1), (2, 1))
        self.assertEqual(ripple_carry_3n1_stats(2), (0, 0))
        self.assertEqual(ripple_carry_3n1_stats(341), (10, 45))
        self.assertEqual(ripple_carry_3n1_stats(682), (0, 0))

        self.assertEqual(binary_nonzero_window_list(1, 0), ())
        self.assertEqual(binary_zero_window_count(1, 0), 0)
        self.assertEqual(binary_nonzero_window_list(5, 1), (1,))
        self.assertEqual(binary_zero_window_count(5, 1), 0)
        self.assertNotEqual(binary_nonzero_window_list(5, 200), binary_nonzero_window_list(5, 400))
        self.assertEqual(binary_nonzero_window_list(5, 800), binary_nonzero_window_list(5, 1600))
        self.assertEqual(binary_zero_window_count(5, 800), 1)
        self.assertEqual(binary_zero_window_count(5, 1600), 2)

        # Trivial loop extension boundary checks (single-bit core [1] and multi-loop m = 0, 1, 2)
        self.assertEqual(trivial_loop_extension((1,), 0), (1, 0, 1))
        self.assertEqual(trivial_loop_extension((1,), 1), (1, 0, 1, 0, 1))
        self.assertEqual(trivial_loop_extension((1, 1), 1), (1, 1, 0, 0, 0, 1, 0, 1))
        self.assertEqual(cft.exact_backward_quotient(1, (1, 1), 0), 3)
        self.assertEqual(
            cft.exact_backward_quotient(1, trivial_loop_extension((1, 1), 2), 0),
            3,
        )

        # Coprime-order prime scan boundary checks
        self.assertEqual(_scan_coprime_order_primes_up_to(5), ())
        self.assertEqual(_scan_coprime_order_primes_up_to(330), ())
        self.assertEqual(_scan_coprime_order_primes_up_to(331), ((331, 30, 11),))

        # Threshold & boundary checks for T_diamond5 and Cone 6
        self.assertFalse(is_diamond5_cone6(237))    # < 2285
        self.assertFalse(is_diamond5_cone6(2029))   # < 2285
        self.assertTrue(is_diamond5_cone6(2285))    # 256 * 9 - 19 (minimal Cone 6 member)
        self.assertFalse(is_diamond5_cone6(256 * 9 * 5 - 19))  # coprime23(x + 19) == 5 != 1
        self.assertEqual(cousin_diamond5_step_int(2285), 857)
        self.assertEqual(cousin_diamond5_step_int(73709), 27641)
        self.assertEqual(cousin_diamond5_block_return(1), (0, 1))
        self.assertEqual(cousin_diamond5_block_return(2), (1, 1))
        self.assertEqual(cousin_diamond5_block_return(2285), (11, 1))
        self.assertEqual(cousin_diamond5_block_return(73709), (16, 1))
        self.assertEqual(cousin_diamond5_block_return(1529), (13, 1))
        self.assertEqual(cousin_diamond5_block_return(3), (1, 5))

        # Verify non-integer Q_(6)^+ rationals (including 2285/7) ALWAYS avoid Cone 6
        from collatz_analysis.cs_cegar_redteam import cousin_diamond4_step_q6
        self.assertEqual(cousin_diamond5_step_q6(Fraction(2285, 7)), Fraction(3431, 7))
        cur_2285_7 = Fraction(2285, 7)
        for _ in range(10):
            cur_2285_7 = cousin_diamond5_step_q6(cur_2285_7)
        self.assertEqual(cur_2285_7, Fraction(1, 7))
        for den in (5, 7, 11, 13):
            for num in (1, 19, 89, 169, 1529, 2285, 2285 * den - 19 * den + 1):
                f_q6 = Fraction(num, den)
                if f_q6.denominator > 1:
                    self.assertEqual(
                        cousin_diamond5_step_q6(f_q6),
                        cousin_diamond4_step_q6(f_q6),
                    )

        # Error-path validation across all Wave 8 primitives
        for bad_n in (-1, True, False, 1.5, "341"):
            with self.assertRaises(ValueError):
                ripple_carry_3n1_stats(bad_n)  # type: ignore[arg-type]
            with self.assertRaises(ValueError):
                binary_nonzero_window_list(3, bad_n)  # type: ignore[arg-type]
            with self.assertRaises(ValueError):
                binary_zero_window_count(3, bad_n)  # type: ignore[arg-type]
        for bad_w in (0, -2, True, False, 2.5, "5"):
            with self.assertRaises(ValueError):
                binary_nonzero_window_list(bad_w, 10)  # type: ignore[arg-type]
            with self.assertRaises(ValueError):
                binary_zero_window_count(bad_w, 10)  # type: ignore[arg-type]
        for bad_u in ((), (0, 1), (1, 0), (1, 2, 1)):
            with self.assertRaises(ValueError):
                trivial_loop_extension(bad_u, 0)
        for bad_m in (-1, True, False, 1.5):
            with self.assertRaises(ValueError):
                trivial_loop_extension((1, 1), bad_m)  # type: ignore[arg-type]
        for bad_max_p in (4, 0, -5, True, False, 5.5):
            with self.assertRaises(ValueError):
                _scan_coprime_order_primes_up_to(bad_max_p)  # type: ignore[arg-type]
        for bad_x in (True, False, 2.5, "2285"):
            with self.assertRaises(ValueError):
                is_diamond5_cone6(bad_x)  # type: ignore[arg-type]
            with self.assertRaises(ValueError):
                cousin_diamond5_step_int(bad_x)  # type: ignore[arg-type]
            with self.assertRaises(ValueError):
                cousin_diamond5_step_q6(bad_x)  # type: ignore[arg-type]
        for bad_q in (1, 2, 4, -3, True):
            with self.assertRaises(ValueError):
                cousin_diamond5_step_int(7, q=bad_q)  # type: ignore[arg-type]
        for bad_pos in (0, -1, True):
            with self.assertRaises(ValueError):
                cousin_diamond5_block_return(bad_pos)  # type: ignore[arg-type]
        for bad_frac in (Fraction(1, 2), Fraction(1, 3), Fraction(5, 6)):
            with self.assertRaises(ValueError):
                cousin_diamond5_step_q6(bad_frac)

        # Synthetic witness-bank check on all 6 Wave 8 dynamic predicates (proving zero hardcoded IDs)
        base_bank = load_witness_bank()
        with tempfile.TemporaryDirectory() as tmpdir:
            synth_bank = copy.deepcopy(base_bank)
            synth_bank["falsified_hypotheses"] = []
            synth_bank["domains"]["z_pos_high_glide"] = [
                {
                    "witness_id": "SYNTH_RIPPLE_21845",
                    "seed": 14563,
                    "next_compressed": 21845,  # (4^8 - 1)//3, % 3 == 2 -> 16 carries vs 0 at 43690
                    "kills_mechanisms": ["ripple_carry_penalty"],
                },
                {
                    "witness_id": "SYNTH_WIN5_3200",
                    "seed": 2133,
                    "next_compressed": 3200,  # 25 * 128 -> identical width-5 windows at 3200 and 6400
                    "kills_mechanisms": ["width5_window"],
                },
                {
                    "witness_id": "SYNTH_D5_CONE6_4589",
                    "seed": 4589,  # 512 * 9 - 19 -> 1721 (Phi_2 jumps upward)
                    "kills_mechanisms": ["phi2_on_diamond5"],
                },
                {
                    "witness_id": "SYNTH_MULTI_LOOP_7",
                    "seed": 7,
                    "core_word": [1, 1, 1],
                    "loop_core_word": list(trivial_loop_extension((1, 1, 1), 2)),
                    "kills_mechanisms": ["single_loop_only"],
                },
            ]
            synth_bank["domains"]["m1_q2_pos"] = [
                {
                    "witness_id": "SYNTH_M1_331_W33_A30",
                    "x0": "1/5",
                    "numerator": 1,
                    "denominator": 5,
                    "period_k": 63,
                    "weight_w": 33,
                    "m_blocks": 1,
                    "kills_mechanisms": ["local_mod331"],
                }
            ]
            synth_bank["domains"]["log2_3_convergents"] = [
                {
                    "witness_id": "SYNTH_SECOND_COPRIME_1210483",
                    "K": 41,
                    "W": 11,
                    "gap_sign": 1,
                    "second_coprime_order_prime": 1210483,
                    "kills_mechanisms": ["unique_331"],
                }
            ]
            synth_p = Path(tmpdir) / "synth_w8.json"
            synth_p.write_text(json.dumps(synth_bank), encoding="utf-8")

            g1 = evaluate_hypothesis_against_witness_bank(
                "SynthRipple", _dynamic_pred_ripple_carry_penalty_monotonicity,
                domains=("z_pos_high_glide",), bank_path=synth_p,
            )
            self.assertEqual(g1["minimal_failure"], ("z_pos_high_glide", "SYNTH_RIPPLE_21845"))
            g2 = evaluate_hypothesis_against_witness_bank(
                "SynthWin5", _dynamic_pred_width5_sliding_window_distinguishes_preimages,
                domains=("z_pos_high_glide",), bank_path=synth_p,
            )
            self.assertEqual(g2["minimal_failure"], ("z_pos_high_glide", "SYNTH_WIN5_3200"))
            g3 = evaluate_hypothesis_against_witness_bank(
                "SynthD5", _dynamic_pred_phi2_on_cousin_diamond5_outside_cones45,
                domains=("z_pos_high_glide",), bank_path=synth_p,
            )
            self.assertEqual(g3["minimal_failure"], ("z_pos_high_glide", "SYNTH_D5_CONE6_4589"))
            g4 = evaluate_hypothesis_against_witness_bank(
                "SynthM1_331", _dynamic_pred_local_mod331_excludes_m1_1block,
                domains=("m1_q2_pos",), bank_path=synth_p,
            )
            self.assertEqual(g4["minimal_failure"], ("m1_q2_pos", "SYNTH_M1_331_W33_A30"))
            g5 = evaluate_hypothesis_against_witness_bank(
                "SynthUnique331", _dynamic_pred_331_unique_coprime_order_prime,
                domains=("log2_3_convergents",), bank_path=synth_p,
            )
            self.assertEqual(g5["minimal_failure"], ("log2_3_convergents", "SYNTH_SECOND_COPRIME_1210483"))
            g6 = evaluate_hypothesis_against_witness_bank(
                "SynthLoop", _dynamic_pred_q0_cross_scale_only_single_loop_collides,
                domains=("z_pos_high_glide",), bank_path=synth_p,
            )
            self.assertEqual(g6["minimal_failure"], ("z_pos_high_glide", "SYNTH_MULTI_LOOP_7"))

            # Verify primary ground-truth corruption detection across all 8 new Wave 8 witnesses
            corruptions = [
                ("z_pos_high_glide", "ZPOS_RIPPLE_CARRY_COLLAPSE_341", "ripple_carry_idx_sum_target", 44),
                ("z_pos_high_glide", "ZPOS_SLIDING_WINDOW_COLLISION_800", "nonzero_windows_target", [16, 8, 4, 18, 25, 12, 6, 3, 2]),
                ("z_pos_high_glide", "ZPOS_COUSIN_DIAMOND5_CONE6_2285_JUMP", "cousin_diamond5_steps_to_1", 12),
                ("z_pos_high_glide", "ZPOS_RAY_Q0_MULTI_LOOP_COLLISION_3", "loop_core_word", [1, 1, 0, 0, 1, 0, 1, 1]),
                ("m1_q2_pos", "M1_331_CANCELLATION_529_OVER_6643574255", "weight_w", 12),
                ("m1_q2_pos", "M1_COUSIN_DIAMOND5_1_OVER_7", "orbit", ["1/7", "5/7", "11/7", "20/7", "3/7"]),
                ("m3_supercritical", "M3_COUSIN_DIAMOND5_7X1_CYCLE5", "orbit", [5, 18, 9, 32, 11]),
                ("log2_3_convergents", "COPRIME_PRIME_1210483_AND_MOD8_SUBGROUP_BARRIER", "second_ord2_mod_p", 91),
            ]
            bad_b = copy.deepcopy(base_bank)
            for dom, wid, field, bad_val in corruptions:
                for item in bad_b["domains"][dom]:
                    if item["witness_id"] == wid:
                        item[field] = bad_val
            bad_p = Path(tmpdir) / "corrupt_w8_all8.json"
            bad_p.write_text(json.dumps(bad_b), encoding="utf-8")
            chk = verify_witness_bank_ground_truth(bad_p)
            self.assertFalse(chk["all_witnesses_ground_truth_verified"])
            for _, wid, _, _ in corruptions:
                self.assertIn(wid, chk["failed_witness_ids"], f"Missed corruption on {wid}")

            # Verify subtle secondary-field corruptions on Wave 8 witnesses
            subtle_corruptions = [
                ("z_pos_high_glide", "ZPOS_RIPPLE_CARRY_COLLAPSE_341", "ripple_carry_count_seed", 5),
                ("z_pos_high_glide", "ZPOS_SLIDING_WINDOW_COLLISION_800", "nonzero_windows_seed", [21, 10, 5, 2, 1, 16, 8, 4, 2, 3]),
                ("z_pos_high_glide", "ZPOS_COUSIN_DIAMOND5_CONE6_2285_JUMP", "phi_diamond2_next", 5849279),
                ("log2_3_convergents", "COPRIME_PRIME_1210483_AND_MOD8_SUBGROUP_BARRIER", "gap_mod8", 3),
            ]
            bad_b2 = copy.deepcopy(base_bank)
            for dom, wid, field, bad_val in subtle_corruptions:
                for item in bad_b2["domains"][dom]:
                    if item["witness_id"] == wid:
                        item[field] = bad_val
            bad_p2 = Path(tmpdir) / "corrupt_w8_subtle.json"
            bad_p2.write_text(json.dumps(bad_b2), encoding="utf-8")
            chk2 = verify_witness_bank_ground_truth(bad_p2)
            self.assertFalse(chk2["all_witnesses_ground_truth_verified"])
            for _, wid, _, _ in subtle_corruptions:
                self.assertIn(wid, chk2["failed_witness_ids"], f"Missed subtle corruption on {wid}")

    def test_wave8_lean4_zero_custom_axioms_docstring_and_pii_audit(self) -> None:
        import re
        from collatz_analysis.formal_proofs import (
            ALLOWED_LEAN4_FOUNDATIONAL_AXIOMS,
            verify_lean4_kernel_proofs,
        )

        pkg_dir = Path(__file__).resolve().parent.parent
        res = verify_lean4_kernel_proofs()
        self.assertTrue(res["pure_kernel_verified"])
        self.assertTrue(res["zero_sorry_verified"])
        self.assertTrue(res["zero_warnings_verified"])
        self.assertGreaterEqual(len(res["lean_files"]), 57)
        self.assertGreaterEqual(res["theorems_audited"], 1839)
        self.assertGreaterEqual(res["axiom_free_theorem_count"], 571)
        self.assertTrue(any(Path(p).name == "Wave8WholeSpace.lean" for p in res["lean_files"]))

        ax_map = res["axioms_by_theorem"]
        w8_theorems = (
            "hofbauer_waldmann_tower_implies_no_infinite_srs_chain",
            "hofbauer_waldmann_tower_acc_srsPlus",
            "all11_hofbauer_waldmann_tower_implies_collatz_standard",
            "omit_r2_10_of_11_admits_single_2d_hw_cert",
            "omit_r7_and_omit_r5_10_of_11_admit_2d_hw_towers",
            "all11_mem_or_omitted",
            "infinite_all11_srs_chain_requires_infinitely_many_r2_r5_r7",
            "arts_giesl_1d_semantic_dp_removes_dp1_rel_all_interior",
            "mixed_srs_interior_b1_and_b0_pumping_identities",
            "omega_k_coord_monotone_and_lower_tri_matrix_tower_impossibility",
            "one_block_exponents_coprime",
            "one_block_cyclotomic_companion_quotient_forcing",
            "prime_11_151_and_331_companion_cert",
            "one_block_331_companion_forcing_and_mod8_obstruction",
            "two_block_331_shared_mersenne_floor_99_159",
            "laurent_binomial_taylor_column_extrapolation_dvd",
            "bernoulli_nat_pow_step",
            "bernoulli_nat_ratio_lt",
            "ripple_carry_alternating_cascade_and_mersenne_triples",
            "berg_meinardus_nonseparable_ripple_carry_preimage_impossibility",
            "berg_meinardus_sliding_window_kgram_impossibility",
            "cousinDiamond5StepInt_ofNat_eq",
            "cousin_diamond5_outside_cones456_strict_descent",
            "cousin_diamond5_cones456_exact_return",
            "cousin_diamond5_global_convergence",
            "cousin_diamond5_r_block_spiral_climb_and_laurent_impossibility",
            "cousin_diamond5_q6_noninteger_avoids_cone6",
            "cousin_diamond5_counter_model_separation",
            "q0_cross_scale_leaf_collision_iff_trivial_loop",
            "multiscale_first_hit_surviving_q0_leaves_nodup",
            "canonicalSuffixShift_markov_bijection_and_mod6_lock",
        )
        for thm in w8_theorems:
            self.assertIn(thm, ax_map)
            self.assertTrue(
                set(ax_map[thm]).issubset(ALLOWED_LEAN4_FOUNDATIONAL_AXIOMS),
                f"Unexpected custom axiom in {thm}: {ax_map[thm]}",
            )

        for axfree_thm in (
            "omit_r2_10_of_11_admits_single_2d_hw_cert",
            "omit_r7_and_omit_r5_10_of_11_admit_2d_hw_towers",
            "arts_giesl_1d_semantic_dp_removes_dp1_rel_all_interior",
            "prime_11_151_and_331_companion_cert",
            "cousin_diamond5_counter_model_separation",
        ):
            self.assertEqual(ax_map[axfree_thm], [], f"Expected [] axioms on {axfree_thm}")
        for choice_free_thm in (
            "all11_mem_or_omitted",
            "one_block_exponents_coprime",
            "one_block_cyclotomic_companion_quotient_forcing",
            "one_block_331_companion_forcing_and_mod8_obstruction",
            "bernoulli_nat_pow_step",
            "bernoulli_nat_ratio_lt",
            "ripple_carry_alternating_cascade_and_mersenne_triples",
            "berg_meinardus_nonseparable_ripple_carry_preimage_impossibility",
            "berg_meinardus_sliding_window_kgram_impossibility",
            "cousin_diamond5_q6_noninteger_avoids_cone6",
        ):
            self.assertNotIn(
                "Classical.choice",
                ax_map[choice_free_thm],
                f"Expected choice-free proof on {choice_free_thm}",
            )

        w8_src = (pkg_dir / "CollatzFormal/Wave8WholeSpace.lean").read_text(encoding="utf-8")
        for doc, thm_name in re.findall(r"/--\s*(.*?)\s*-/\s*theorem\s+([A-Za-z0-9_']+)\b", w8_src, flags=re.S):
            if "`[]` axioms" in doc:
                self.assertEqual(ax_map.get(thm_name), [], f"False []-axiom docstring on {thm_name}")
            if "choice-free" in doc:
                self.assertNotIn("Classical.choice", ax_map.get(thm_name, []), f"False choice-free docstring on {thm_name}")
        axfree_claim_pats = (
            re.compile(r"`([A-Za-z0-9_']+)`\s*\(`\[\]`\s*axioms", flags=re.I),
            re.compile(r"`([A-Za-z0-9_']+)`\s*,\s*`\[\]`\s*axioms", flags=re.I),
        )
        for doc_rel in (
            "CollatzFormal/Wave8WholeSpace.lean",
            "PROOF_SPACE_LEDGER.md",
            "MATHEMATICAL_FINDINGS.md",
            "README.md",
        ):
            doc_txt = (pkg_dir / doc_rel).read_text(encoding="utf-8")
            for pat in axfree_claim_pats:
                for thm_ref in pat.findall(doc_txt):
                    self.assertEqual(
                        ax_map.get(thm_ref),
                        [],
                        f"False []-axiom claim in {doc_rel} on {thm_ref}: {ax_map.get(thm_ref)}",
                    )
        self.assertNotIn("(`[]` Axioms)", w8_src)

        # Repo-wide zero-PII / machine-path hygiene scan across tracked source & docs
        forbidden_tokens = (
            "Us" + "ers" + "\\",
            "Us" + "ers/",
            "/" + "home" + "/",
            "C:" + "\\",
            "C:" + "/",
        )
        for path in sorted(pkg_dir.rglob("*")):
            if ".lake" in path.parts or "__pycache__" in path.parts or path.is_dir():
                continue
            if path.suffix in {".py", ".lean", ".md", ".json", ".c"}:
                txt = path.read_text(encoding="utf-8")
                for tok in forbidden_tokens:
                    self.assertNotIn(tok, txt, f"Forbidden path token {tok!r} in {path.name}")

    def test_cli_summary_includes_wave8_loop_and_exit_gate(self) -> None:
        import contextlib
        import io
        from unittest import mock
        from collatz_analysis.cli import main as cli_main

        buf_sum = io.StringIO()
        with contextlib.redirect_stdout(buf_sum):
            rc_sum = cli_main(["--summary", "--dp-depth", "50"])
        self.assertEqual(rc_sum, 0)
        out = buf_sum.getvalue()
        self.assertIn("[Wave 8 Whole-Space Proof Loop]", out)
        self.assertIn("A=True, B=True", out)
        self.assertIn("C=True, T_diamond5=True, D=True", out)
        self.assertLess(
            out.index("[Wave 7 Whole-Space Proof Loop]"),
            out.index("[Wave 8 Whole-Space Proof Loop]"),
        )
        self.assertLess(
            out.index("[Wave 8 Whole-Space Proof Loop]"),
            out.index("[Lean 4 Kernel Verification]"),
        )

        failed_w8 = {
            "passed": False,
            "verdict": "FALSIFIED",
            "universality_gate_passed": True,
            "witness_bank_total_entries": 61,
            "witness_bank_falsified_count": 24,
            "witness_bank_ground_truth_verified": True,
            "front_a_srs_10_of_11_and_towers": {
                "omit_r2_10_of_11_single_2d_cert_verified": False,
                "omit_r7_10_of_11_2level_2d_tower_verified": True,
                "omit_r5_10_of_11_3level_2d_tower_verified": True,
                "arts_giesl_1d_semantic_dp_verified": True,
                "interior_pumping_and_omega_k_stall_verified": True,
            },
            "front_b_cyclotomic_331_and_laurent": {
                "exact_first_two_coprime_primes_verified": True,
                "companion_factorizations_and_m1_cancellation_verified": True,
                "twoblock_331_floor_99_159_verified": True,
                "laurent_taylor_column_extrapolation_verified": True,
            },
            "front_c_ripple_window_and_diamond5": {
                "ripple_carry_cascade_mersenne_and_bernoulli_verified": True,
                "sliding_window_kgram_family_verified": True,
                "cousin_diamond5_outside_cones456_descent_verified": False,
                "cousin_diamond5_cone6_return_and_spiral_verified": True,
                "cousin_diamond5_countermodels_verified": True,
            },
            "front_d_cross_scale_and_markov_mod6": {
                "cross_scale_q0_biconditional_verified": True,
                "multiscale_surviving_q0_nodup_verified": True,
                "markov_bijection_and_mod6_lock_verified": False,
            },
        }
        buf_fail = io.StringIO()
        with mock.patch(
            "collatz_analysis.cs_cegar_redteam.run_wave8_whole_space_campaign",
            return_value=failed_w8,
        ), mock.patch(
            "collatz_analysis.cli.verify_lean4_kernel_proofs",
            return_value={"lean_available": False, "static_hygiene_clean": True},
        ), contextlib.redirect_stdout(buf_fail):
            rc_fail = cli_main(["--summary", "--dp-depth", "10"])
        self.assertEqual(rc_fail, 1)
        self.assertIn("A=False", buf_fail.getvalue())
        self.assertIn("T_diamond5=False", buf_fail.getvalue())
        self.assertIn("D=False", buf_fail.getvalue())


class TestWave9WholeSpaceCampaign(unittest.TestCase):
    """Deep unit, edge-case, corruption, and Lean 4 kernel tests for Wave 9."""

    def test_wave9_exports_witness_bank_and_all_four_fronts(self) -> None:
        import collatz_analysis as ca
        from collatz_analysis.cs_cegar_redteam import (
            audit_w9_front_a_srs_d2_barrier_d3_omit_r9_and_zantema,
            audit_w9_front_b_laurent_4x4_twobase_and_coprime_sieve,
            audit_w9_front_c_stateful_automaton_barrier_and_diamond6,
            audit_w9_front_d_global_collision_and_markov_pow3,
            load_witness_bank,
            run_wave9_whole_space_campaign,
            verify_witness_bank_ground_truth,
        )

        for exported_sym in (
            "run_lsb_automaton",
            "run_msb_automaton",
            "run_lsb_transducer",
            "run_msb_transducer",
            "loop_unroll_word",
            "is_diamond6_cone7",
            "cousin_diamond6_step_int",
            "cousin_diamond6_step_q6",
            "cousin_diamond6_block_return",
            "audit_w9_front_a_srs_d2_barrier_d3_omit_r9_and_zantema",
            "audit_w9_front_b_laurent_4x4_twobase_and_coprime_sieve",
            "audit_w9_front_c_stateful_automaton_barrier_and_diamond6",
            "audit_w9_front_d_global_collision_and_markov_pow3",
            "run_wave9_whole_space_campaign",
        ):
            self.assertTrue(hasattr(ca, exported_sym), f"Missing package export: {exported_sym}")

        bank = load_witness_bank()
        self.assertGreaterEqual(len(bank["domains"]["z_pos_high_glide"]), 27)
        self.assertGreaterEqual(len(bank["domains"]["m1_q2_pos"]), 15)
        self.assertGreaterEqual(len(bank["domains"]["m2_z_neg"]), 4)
        self.assertGreaterEqual(len(bank["domains"]["m3_supercritical"]), 9)
        self.assertGreaterEqual(len(bank["domains"]["log2_3_convergents"]), 13)
        self.assertGreaterEqual(sum(len(v) for v in bank["domains"].values()), 68)
        self.assertGreaterEqual(len(bank["falsified_hypotheses"]), 28)

        truth = verify_witness_bank_ground_truth()
        self.assertTrue(truth["all_witnesses_ground_truth_verified"])
        self.assertGreaterEqual(truth["verified_witness_count"], 68)
        self.assertEqual(truth["failed_witness_ids"], ())

        w9 = run_wave9_whole_space_campaign()
        self.assertTrue(w9["passed"])
        self.assertEqual(w9["verdict"], "REDTEAM-PASSED")
        self.assertTrue(w9["universality_gate_passed"])
        self.assertGreaterEqual(w9["witness_bank_total_entries"], 68)
        self.assertGreaterEqual(w9["witness_bank_falsified_count"], 28)

        fa = audit_w9_front_a_srs_d2_barrier_d3_omit_r9_and_zantema()
        self.assertTrue(fa["omit_r9_10_of_11_5level_3d_tower_verified"])
        self.assertTrue(fa["zantema_mod_m_semantic_algebra_verified"])
        self.assertTrue(fa["s9_mod2_labelled_7level_2d_tower_verified"])
        self.assertTrue(fa["s9_subseq_pumping_zero_diag_obstruction_verified"])
        self.assertTrue(fa["s9_parikh_syzygy_and_boundary_nontri_2d_collapse_verified"])

        fb = audit_w9_front_b_laurent_4x4_twobase_and_coprime_sieve()
        self.assertTrue(fb["laurent_4x4_three_closed_forms_and_cone_verified"])
        self.assertTrue(fb["twobase_4x4_resonant_zero_9_16_2_verified"])
        self.assertTrue(fb["coprime_primes_p3_45661129_and_p4_107889071_verified"])
        self.assertTrue(fb["joint_331_and_107889071_floors_verified"])
        self.assertTrue(fb["solo_p3_p4_companion_quotient_forcing_verified"])

        fc = audit_w9_front_c_stateful_automaton_barrier_and_diamond6()
        self.assertTrue(fc["stateful_automaton_q_factorial_family_verified"])
        self.assertTrue(fc["stateful_transducer_affine_and_mersenne_barrier_verified"])
        self.assertTrue(fc["cousin_diamond6_outside_cones4567_descent_verified"])
        self.assertTrue(fc["cousin_diamond6_cone7_return_and_spiral_verified"])
        self.assertTrue(fc["cousin_diamond6_countermodels_verified"])

        fd = audit_w9_front_d_global_collision_and_markov_pow3()
        self.assertGreater(fd["mixed_q0_qpos_collisions_found"], 0)
        self.assertTrue(fd["global_all_pairs_classification_verified"])
        self.assertTrue(fd["global_first_hit_injectivity_verified"])
        self.assertTrue(fd["markov_mod18_and_pow3_memory_annihilation_verified"])
        self.assertTrue(fd["markov_mod18_table_and_multistep_equidistribution_verified"])

    def test_wave9_edge_cases_error_paths_and_witness_corruption(self) -> None:
        import copy
        from fractions import Fraction
        import json
        import tempfile
        from collatz_analysis import cs_forest_transfer as cft
        from collatz_analysis.cs_cegar_redteam import (
            _dynamic_pred_mixed_q0_qpos_raw_disjointness,
            _dynamic_pred_phi2_on_cousin_diamond6_outside_cones456,
            _dynamic_pred_stateful_q2_automaton_distinguishes_multi_even,
            _dynamic_pred_third_coprime_prime_escapes_mod8_13,
            _dynamic_pred_twobase_4x4_laurent_det_nonzero_for_all_coprime,
            cousin_diamond5_step_q6,
            cousin_diamond6_block_return,
            cousin_diamond6_step_int,
            cousin_diamond6_step_q6,
            evaluate_hypothesis_against_witness_bank,
            is_diamond6_cone7,
            load_witness_bank,
            loop_unroll_word,
            run_lsb_automaton,
            run_lsb_transducer,
            run_msb_automaton,
            run_msb_transducer,
            trivial_loop_extension,
            verify_witness_bank_ground_truth,
        )

        # Boundary checks for LSB/MSB automata & Mealy transducers (n = 0, 1, 2, 800, 1600, 3200, Mersenne)
        zero_parity_tbl = [(1, 0), (0, 1)]
        self.assertEqual(run_lsb_automaton(2, zero_parity_tbl, 0, 0), 0)
        self.assertEqual(run_msb_automaton(2, zero_parity_tbl, 0, 0), 0)
        self.assertEqual(run_lsb_automaton(2, zero_parity_tbl, 1, 0), 1)
        self.assertEqual(run_msb_automaton(2, zero_parity_tbl, 1, 0), 1)
        self.assertEqual(run_lsb_transducer(2, zero_parity_tbl, [(1, 2), (3, 4)], 0, 0), 0)
        self.assertEqual(run_msb_transducer(2, zero_parity_tbl, [(1, 2), (3, 4)], 0, 0), 0)
        # Parity-of-popcount Q = 2 Mealy transducer emits 0 on all 0-transitions (constant on 800 vs 3200),
        # yet grows linearly along Mersenne 1-spines 2^k - 1!
        pop_parity_tbl = [(0, 1), (1, 0)]
        pop_emit_tbl = [(0, 1), (0, 0)]
        self.assertEqual(
            run_msb_transducer(2, pop_parity_tbl, pop_emit_tbl, 0, 800),
            run_msb_transducer(2, pop_parity_tbl, pop_emit_tbl, 0, 3200),
        )
        self.assertEqual(run_msb_transducer(2, pop_parity_tbl, pop_emit_tbl, 0, (1 << 10) - 1), 5)
        # Q = 2 zero-parity separates 800 vs 1600 yet collides on 800 vs 3200!
        self.assertNotEqual(
            run_lsb_automaton(2, zero_parity_tbl, 0, 800),
            run_lsb_automaton(2, zero_parity_tbl, 0, 1600),
        )
        self.assertEqual(
            run_lsb_automaton(2, zero_parity_tbl, 0, 800),
            run_lsb_automaton(2, zero_parity_tbl, 0, 3200),
        )
        self.assertEqual(
            run_msb_automaton(2, zero_parity_tbl, 0, 800),
            run_msb_automaton(2, zero_parity_tbl, 0, 3200),
        )

        # Boundary checks for loop_unroll_word (q = 0 vs q >= 1)
        self.assertEqual(loop_unroll_word((1,), 0, 0), trivial_loop_extension((1,), 0))
        self.assertEqual(loop_unroll_word((1, 1), 0, 2), trivial_loop_extension((1, 1), 2))
        self.assertEqual(loop_unroll_word((1,), 1, 0), (1, 0, 0, 0, 1))
        self.assertEqual(loop_unroll_word((1,), 1, 1), (1, 0, 0, 0, 1, 0, 1))
        self.assertEqual(
            cft.exact_backward_quotient(1, loop_unroll_word((1,), 1, 1), 0),
            cft.exact_backward_quotient(1, (1,), 1),
        )
        self.assertEqual(cft.exact_backward_quotient(1, (1,), 1), 5)

        # Threshold & boundary checks for T_diamond6 and Cone 7
        self.assertFalse(is_diamond6_cone7(31_957))        # < 294101
        self.assertFalse(is_diamond6_cone7(294_100))       # < 294101
        self.assertTrue(is_diamond6_cone7(294_101))        # 32768 * 9 - 811 (minimal Cone 7 member)
        self.assertFalse(is_diamond6_cone7(32_768 * 9 * 5 - 811))  # coprime23(x + 811) == 5 != 1
        self.assertTrue(is_diamond6_cone7(21_232_853))     # 2^18 * 81 - 811
        self.assertEqual(cousin_diamond6_step_int(294_101), 6_893)
        self.assertEqual(cousin_diamond6_step_int(6_893), 2_585)
        self.assertEqual(cousin_diamond6_step_int(21_232_853), 497_645)
        self.assertEqual(cousin_diamond6_step_int(497_645), 186_617)
        self.assertEqual(cousin_diamond6_block_return(1), (0, 1))
        self.assertEqual(cousin_diamond6_block_return(2), (1, 1))
        self.assertEqual(cousin_diamond6_block_return(294_101), (13, 1))
        self.assertEqual(cousin_diamond6_block_return(21_232_853), (19, 1))
        self.assertEqual(cousin_diamond6_block_return(2_285), (11, 1))
        self.assertEqual(cousin_diamond6_block_return(3), (1, 5))

        # Verify non-integer Q_(6)^+ rationals (including 294101/7) ALWAYS avoid Cone 7
        cur_294101_7 = Fraction(294_101, 7)
        for _ in range(19):
            cur_294101_7 = cousin_diamond6_step_q6(cur_294101_7)
        self.assertEqual(cur_294101_7, Fraction(1, 7))
        for den in (5, 7, 11, 13):
            for num in (1, 19, 2_285, 294_101, 294_101 * den - 811 * den + 1):
                f_q6 = Fraction(num, den)
                if f_q6.denominator > 1:
                    self.assertEqual(
                        cousin_diamond6_step_q6(f_q6),
                        cousin_diamond5_step_q6(f_q6),
                    )

        # Error-path validation across all Wave 9 primitives
        for fn in (run_lsb_automaton, run_msb_automaton):
            for bad_q in (0, -1, True, False, 1.5, "2"):
                with self.assertRaises(ValueError):
                    fn(bad_q, [(0, 0)], 0, 5)  # type: ignore[arg-type]
            for bad_tbl in ([], [(0,)], [(0, 2)], [(0, True)], "00"):
                with self.assertRaises(ValueError):
                    fn(1, bad_tbl, 0, 5)  # type: ignore[arg-type]
            for bad_init in (-1, 1, True, False, "0"):
                with self.assertRaises(ValueError):
                    fn(1, [(0, 0)], bad_init, 5)  # type: ignore[arg-type]
            for bad_n in (-1, True, False, 2.5, "800"):
                with self.assertRaises(ValueError):
                    fn(1, [(0, 0)], 0, bad_n)  # type: ignore[arg-type]

        for tfn in (run_lsb_transducer, run_msb_transducer):
            for bad_emit in ([], [(1,)], [(-1, 0)], [(0, True)], "00"):
                with self.assertRaises(ValueError):
                    tfn(1, [(0, 0)], bad_emit, 0, 5)  # type: ignore[arg-type]

        for bad_u in ((), (0, 1), (1, 0), (1, 2, 1), (True,), "1"):
            with self.assertRaises(ValueError):
                loop_unroll_word(bad_u, 1, 0)  # type: ignore[arg-type]
        for bad_qm in (-1, True, False, 1.5, "1"):
            with self.assertRaises(ValueError):
                loop_unroll_word((1,), bad_qm, 0)  # type: ignore[arg-type]
            with self.assertRaises(ValueError):
                loop_unroll_word((1,), 1, bad_qm)  # type: ignore[arg-type]

        for bad_x in (True, False, 2.5, "294101"):
            with self.assertRaises(ValueError):
                is_diamond6_cone7(bad_x)  # type: ignore[arg-type]
            with self.assertRaises(ValueError):
                cousin_diamond6_step_int(bad_x)  # type: ignore[arg-type]
            with self.assertRaises(ValueError):
                cousin_diamond6_step_q6(bad_x)  # type: ignore[arg-type]
        for bad_q in (1, 2, 4, -3, True):
            with self.assertRaises(ValueError):
                cousin_diamond6_step_int(7, q=bad_q)  # type: ignore[arg-type]
        for bad_pos in (0, -1, True):
            with self.assertRaises(ValueError):
                cousin_diamond6_block_return(bad_pos)  # type: ignore[arg-type]
        for bad_frac in (Fraction(1, 2), Fraction(1, 3), Fraction(5, 6)):
            with self.assertRaises(ValueError):
                cousin_diamond6_step_q6(bad_frac)

        # Synthetic witness-bank check on all 5 Wave 9 dynamic predicates (proving zero hardcoded IDs)
        base_bank = load_witness_bank()
        with tempfile.TemporaryDirectory() as tmpdir:
            synth_bank = copy.deepcopy(base_bank)
            synth_bank["falsified_hypotheses"] = []
            synth_bank["domains"]["z_pos_high_glide"] = [
                {
                    "witness_id": "SYNTH_STATEFUL_Q2_12320_VS_49280",
                    "seed": 8213,
                    "next_compressed": 12320,  # m_{2,1} = 3 * 4^6 + 32
                    "multi_even_preimage": 49280,  # 4 * 12320
                    "kills_mechanisms": ["stateful_q2"],
                },
                {
                    "witness_id": "SYNTH_D6_CONE7_1358953685",
                    "seed": 1358953685,  # 2^24 * 81 - 811 -> 31850477 (Phi_2 jumps upward)
                    "kills_mechanisms": ["phi2_on_diamond6"],
                },
                {
                    "witness_id": "SYNTH_MIXED_RAY_21",
                    "seed": 21,
                    "core_word": [1],
                    "q_index": 2,
                    "mixed_q0_unroll_word": list(loop_unroll_word((1,), 2, 1)),
                    "kills_mechanisms": ["mixed_q0_qpos"],
                },
            ]
            synth_bank["domains"]["log2_3_convergents"] = [
                {
                    "witness_id": "SYNTH_TWOBASE_RESONANT_W27_K64_U4",
                    "W": 27,
                    "K": 64,
                    "gap_sign": 1,
                    "laurent_twobase_4x4_u": 4,  # 27^2 * 16 * 80^2 == 64^2 * 81 * 15^2
                    "kills_mechanisms": ["twobase_4x4"],
                },
                {
                    "witness_id": "SYNTH_THIRD_COPRIME_MOD8_1",
                    "W": 11,
                    "K": 41,
                    "gap_sign": 1,
                    "third_coprime_order_prime": 45_661_129,
                    "kills_mechanisms": ["third_coprime_mod8"],
                },
            ]
            synth_p = Path(tmpdir) / "synth_w9.json"
            synth_p.write_text(json.dumps(synth_bank), encoding="utf-8")

            g1 = evaluate_hypothesis_against_witness_bank(
                "SynthStatefulQ2", _dynamic_pred_stateful_q2_automaton_distinguishes_multi_even,
                domains=("z_pos_high_glide",), bank_path=synth_p,
            )
            self.assertEqual(g1["minimal_failure"], ("z_pos_high_glide", "SYNTH_STATEFUL_Q2_12320_VS_49280"))
            g2 = evaluate_hypothesis_against_witness_bank(
                "SynthD6", _dynamic_pred_phi2_on_cousin_diamond6_outside_cones456,
                domains=("z_pos_high_glide",), bank_path=synth_p,
            )
            self.assertEqual(g2["minimal_failure"], ("z_pos_high_glide", "SYNTH_D6_CONE7_1358953685"))
            g3 = evaluate_hypothesis_against_witness_bank(
                "SynthTwoBase4x4", _dynamic_pred_twobase_4x4_laurent_det_nonzero_for_all_coprime,
                domains=("log2_3_convergents",), bank_path=synth_p,
            )
            self.assertEqual(g3["minimal_failure"], ("log2_3_convergents", "SYNTH_TWOBASE_RESONANT_W27_K64_U4"))
            g4 = evaluate_hypothesis_against_witness_bank(
                "SynthThirdPrime", _dynamic_pred_third_coprime_prime_escapes_mod8_13,
                domains=("log2_3_convergents",), bank_path=synth_p,
            )
            self.assertEqual(g4["minimal_failure"], ("log2_3_convergents", "SYNTH_THIRD_COPRIME_MOD8_1"))
            g5 = evaluate_hypothesis_against_witness_bank(
                "SynthMixedRay", _dynamic_pred_mixed_q0_qpos_raw_disjointness,
                domains=("z_pos_high_glide",), bank_path=synth_p,
            )
            self.assertEqual(g5["minimal_failure"], ("z_pos_high_glide", "SYNTH_MIXED_RAY_21"))

            # Verify primary ground-truth corruption detection across all 7 new Wave 9 witnesses
            corruptions = [
                ("z_pos_high_glide", "ZPOS_STATEFUL_Q2_COLLISION_800_VS_3200", "multi_even_preimage", 1600),
                ("z_pos_high_glide", "ZPOS_COUSIN_DIAMOND6_CONE7_21232853_JUMP", "cousin_diamond6_steps_to_1", 18),
                ("z_pos_high_glide", "ZPOS_RAY_MIXED_Q0_Q1_COLLISION_5", "mixed_q0_unroll_word", [1, 0, 0, 1, 0, 1]),
                ("m1_q2_pos", "M1_COUSIN_DIAMOND6_1_OVER_7", "orbit", ["1/7", "5/7", "11/7", "20/7", "3/7"]),
                ("m3_supercritical", "M3_COUSIN_DIAMOND6_7X1_CYCLE5", "orbit", [5, 18, 9, 32, 11]),
                ("log2_3_convergents", "LAURENT_TWOBASE_4X4_RESONANT_ZERO_W9_K16_U2", "laurent_twobase_4x4_det", 1),
                ("log2_3_convergents", "COPRIME_PRIMES_45661129_MOD8_1_AND_107889071_MOD8_7", "fourth_ord2_mod_p", 10567),
            ]
            bad_b = copy.deepcopy(base_bank)
            for dom, wid, field, bad_val in corruptions:
                for item in bad_b["domains"][dom]:
                    if item["witness_id"] == wid:
                        item[field] = bad_val
            bad_p = Path(tmpdir) / "corrupt_w9_all7.json"
            bad_p.write_text(json.dumps(bad_b), encoding="utf-8")
            chk = verify_witness_bank_ground_truth(bad_p)
            self.assertFalse(chk["all_witnesses_ground_truth_verified"])
            for _, wid, _, _ in corruptions:
                self.assertIn(wid, chk["failed_witness_ids"], f"Missed corruption on {wid}")

            # Verify subtle secondary-field corruptions on Wave 9 witnesses
            subtle_corruptions = [
                ("z_pos_high_glide", "ZPOS_STATEFUL_Q2_COLLISION_800_VS_3200", "multi_even_step_exp", 3),
                ("z_pos_high_glide", "ZPOS_COUSIN_DIAMOND6_CONE7_21232853_JUMP", "phi_diamond2_next", 42264334361375),
                ("log2_3_convergents", "LAURENT_TWOBASE_4X4_RESONANT_ZERO_W9_K16_U2", "laurent_twobase_4x4_u", 1),
                ("log2_3_convergents", "COPRIME_PRIMES_45661129_MOD8_1_AND_107889071_MOD8_7", "third_ord32_mod_p", 922),
            ]
            bad_b2 = copy.deepcopy(base_bank)
            for dom, wid, field, bad_val in subtle_corruptions:
                for item in bad_b2["domains"][dom]:
                    if item["witness_id"] == wid:
                        item[field] = bad_val
            bad_p2 = Path(tmpdir) / "corrupt_w9_subtle.json"
            bad_p2.write_text(json.dumps(bad_b2), encoding="utf-8")
            chk2 = verify_witness_bank_ground_truth(bad_p2)
            self.assertFalse(chk2["all_witnesses_ground_truth_verified"])
            for _, wid, _, _ in subtle_corruptions:
                self.assertIn(wid, chk2["failed_witness_ids"], f"Missed subtle corruption on {wid}")

    def test_wave9_lean4_zero_custom_axioms_docstring_and_pii_audit(self) -> None:
        import re
        from collatz_analysis.formal_proofs import (
            ALLOWED_LEAN4_FOUNDATIONAL_AXIOMS,
            verify_lean4_kernel_proofs,
        )

        pkg_dir = Path(__file__).resolve().parent.parent
        res = verify_lean4_kernel_proofs()
        self.assertTrue(res["pure_kernel_verified"])
        self.assertTrue(res["zero_sorry_verified"])
        self.assertTrue(res["zero_warnings_verified"])
        self.assertGreaterEqual(len(res["lean_files"]), 58)
        self.assertGreaterEqual(res["theorems_audited"], 1985)
        self.assertGreaterEqual(res["axiom_free_theorem_count"], 592)
        self.assertTrue(any(Path(p).name == "Wave9WholeSpace.lean" for p in res["lean_files"]))

        ax_map = res["axioms_by_theorem"]
        w9_theorems = (
            "omit_r9_10_of_11_admits_3d_hw_tower",
            "infinite_all11_srs_chain_requires_infinitely_many_r2_r5_r7_r9",
            "collatz_mod_m_is_exact_semantic_model",
            "zantema_semantic_labelling_soundness",
            "s9_mod2_labelled_admits_2d_hw_tower",
            "no_infinite_s9_srs_chain",
            "s9_subseq_pumping_and_d2_zero_diag_obstruction",
            "s9_d2_interior_lower_tri_level_collapse",
            "s9_d2_boundary_nontri_and_parikh_syzygy_obstruction",
            "laurent_4x4_confluent_and_twobase_nonvanishing",
            "nat_func_pigeonhole",
            "gauss_euclid_lemma",
            "lucas_order_implies_isPrimeNat",
            "coprime_primes_45661129_and_107889071_cert",
            "w9_joint_lcm_arith_cert",
            "one_block_331_forces_mod8_escape_and_joint_p4_floors",
            "p3_p4_companion_arith_cert",
            "p3_and_p4_cyclotomic_companion_quotient_forcing",
            "fin_unary_iter_factorial_period",
            "berg_meinardus_stateful_automaton_preimage_impossibility",
            "fin_unary_iter_and_sum_period_sub1",
            "berg_meinardus_stateful_transducer_preimage_impossibility",
            "cousinDiamond6StepInt_ofNat_eq",
            "cousin_diamond6_outside_cones4567_strict_descent",
            "not_cone7_six_mul_pow9_sub1",
            "cousin_diamond6_cones4567_exact_return",
            "cousin_diamond6_global_convergence",
            "cousin_diamond6_r_block_spiral_climb_and_laurent_impossibility",
            "cousin_diamond6_q6_noninteger_avoids_cone7",
            "cousin_diamond6_counter_model_separation",
            "one_generator_q_pos_all_weights_first_hit",
            "global_one_generator_collision_classification",
            "canonicalSuffixShift_mod18_and_pow3_memory_annihilation",
            "nat_fin_inj_implies_surj",
            "markovShift_mod18_bijection_and_multistep_fiber_equidistribution",
        )
        for thm in w9_theorems:
            self.assertIn(thm, ax_map)
            self.assertTrue(
                set(ax_map[thm]).issubset(ALLOWED_LEAN4_FOUNDATIONAL_AXIOMS),
                f"Unexpected custom axiom in {thm}: {ax_map[thm]}",
            )

        for axfree_thm in (
            "omit_r9_10_of_11_admits_3d_hw_tower",
            "s9_mod2_labelled_admits_2d_hw_tower",
            "w9_joint_lcm_arith_cert",
            "p3_p4_companion_arith_cert",
            "cousin_diamond6_counter_model_separation",
        ):
            self.assertEqual(ax_map[axfree_thm], [], f"Expected [] axioms on {axfree_thm}")

        for choice_free_thm in (
            "collatz_mod_m_is_exact_semantic_model",
            "nat_func_pigeonhole",
            "gauss_euclid_lemma",
            "lucas_order_implies_isPrimeNat",
            "coprime_primes_45661129_and_107889071_cert",
            "p3_and_p4_cyclotomic_companion_quotient_forcing",
            "fin_unary_iter_factorial_period",
            "berg_meinardus_stateful_automaton_preimage_impossibility",
            "fin_unary_iter_and_sum_period_sub1",
            "berg_meinardus_stateful_transducer_preimage_impossibility",
            "cousin_diamond6_q6_noninteger_avoids_cone7",
            "nat_fin_inj_implies_surj",
        ):
            self.assertNotIn(
                "Classical.choice",
                ax_map[choice_free_thm],
                f"Expected choice-free proof on {choice_free_thm}",
            )

        w9_src = (pkg_dir / "CollatzFormal/Wave9WholeSpace.lean").read_text(encoding="utf-8")
        for doc, thm_name in re.findall(r"/--\s*(.*?)\s*-/\s*theorem\s+([A-Za-z0-9_']+)\b", w9_src, flags=re.S):
            if "`[]` axioms" in doc:
                self.assertEqual(ax_map.get(thm_name), [], f"False []-axiom docstring on {thm_name}")
            if "choice-free" in doc:
                self.assertNotIn("Classical.choice", ax_map.get(thm_name, []), f"False choice-free docstring on {thm_name}")
        axfree_claim_pats = (
            re.compile(r"`([A-Za-z0-9_']+)`\s*\(`\[\]`\s*axioms", flags=re.I),
            re.compile(r"`([A-Za-z0-9_']+)`\s*,\s*`\[\]`\s*axioms", flags=re.I),
        )
        for doc_rel in (
            "CollatzFormal/Wave9WholeSpace.lean",
            "PROOF_SPACE_LEDGER.md",
            "MATHEMATICAL_FINDINGS.md",
            "README.md",
        ):
            doc_txt = (pkg_dir / doc_rel).read_text(encoding="utf-8")
            for pat in axfree_claim_pats:
                for thm_ref in pat.findall(doc_txt):
                    self.assertEqual(
                        ax_map.get(thm_ref),
                        [],
                        f"False []-axiom claim in {doc_rel} on {thm_ref}: {ax_map.get(thm_ref)}",
                    )
        self.assertNotIn("(`[]` Axioms)", w9_src)

        # Repo-wide zero-PII / machine-path hygiene scan across tracked source & docs
        forbidden_tokens = (
            "Us" + "ers" + "\\",
            "Us" + "ers/",
            "/" + "home" + "/",
            "C:" + "\\",
            "C:" + "/",
        )
        for path in sorted(pkg_dir.rglob("*")):
            if ".lake" in path.parts or "__pycache__" in path.parts or path.is_dir():
                continue
            if path.suffix in {".py", ".lean", ".md", ".json", ".c"}:
                txt = path.read_text(encoding="utf-8")
                for tok in forbidden_tokens:
                    self.assertNotIn(tok, txt, f"Forbidden path token {tok!r} in {path.name}")

    def test_cli_summary_includes_wave9_loop_and_exit_gate(self) -> None:
        import contextlib
        import io
        from unittest import mock
        from collatz_analysis.cli import main as cli_main

        buf_sum = io.StringIO()
        with contextlib.redirect_stdout(buf_sum):
            rc_sum = cli_main(["--summary", "--dp-depth", "50"])
        self.assertEqual(rc_sum, 0)
        out = buf_sum.getvalue()
        self.assertIn("[Wave 9 Whole-Space Proof Loop]", out)
        self.assertIn("A=True, B=True", out)
        self.assertIn("C=True, T_diamond6=True, D=True", out)
        self.assertLess(
            out.index("[Wave 8 Whole-Space Proof Loop]"),
            out.index("[Wave 9 Whole-Space Proof Loop]"),
        )
        self.assertLess(
            out.index("[Wave 9 Whole-Space Proof Loop]"),
            out.index("[Lean 4 Kernel Verification]"),
        )

        failed_w9 = {
            "passed": False,
            "verdict": "FALSIFIED",
            "universality_gate_passed": True,
            "witness_bank_total_entries": 68,
            "witness_bank_falsified_count": 28,
            "witness_bank_ground_truth_verified": True,
            "front_a_srs_d3_and_zantema": {
                "omit_r9_10_of_11_5level_3d_tower_verified": False,
                "zantema_mod_m_semantic_algebra_verified": True,
                "s9_mod2_labelled_7level_2d_tower_verified": True,
                "s9_subseq_pumping_zero_diag_obstruction_verified": True,
                "s9_parikh_syzygy_and_boundary_nontri_2d_collapse_verified": True,
            },
            "front_b_laurent_4x4_and_coprime_sieve": {
                "laurent_4x4_three_closed_forms_and_cone_verified": True,
                "twobase_4x4_resonant_zero_9_16_2_verified": True,
                "coprime_primes_p3_45661129_and_p4_107889071_verified": True,
                "joint_331_and_107889071_floors_verified": True,
                "solo_p3_p4_companion_quotient_forcing_verified": True,
            },
            "front_c_stateful_automaton_and_diamond6": {
                "stateful_automaton_q_factorial_family_verified": True,
                "stateful_transducer_affine_and_mersenne_barrier_verified": True,
                "cousin_diamond6_outside_cones4567_descent_verified": False,
                "cousin_diamond6_cone7_return_and_spiral_verified": True,
                "cousin_diamond6_countermodels_verified": True,
            },
            "front_d_global_collision_and_markov_pow3": {
                "global_all_pairs_classification_verified": True,
                "global_first_hit_injectivity_verified": True,
                "markov_mod18_and_pow3_memory_annihilation_verified": False,
                "markov_mod18_table_and_multistep_equidistribution_verified": True,
            },
        }
        buf_fail = io.StringIO()
        with mock.patch(
            "collatz_analysis.cs_cegar_redteam.run_wave9_whole_space_campaign",
            return_value=failed_w9,
        ), mock.patch(
            "collatz_analysis.cli.verify_lean4_kernel_proofs",
            return_value={"lean_available": False, "static_hygiene_clean": True},
        ), contextlib.redirect_stdout(buf_fail):
            rc_fail = cli_main(["--summary", "--dp-depth", "10"])
        self.assertEqual(rc_fail, 1)
        self.assertIn("A=False", buf_fail.getvalue())
        self.assertIn("T_diamond6=False", buf_fail.getvalue())
        self.assertIn("D=False", buf_fail.getvalue())


class TestWave10WholeSpaceCampaign(unittest.TestCase):
    """Wave 10 whole-space campaign, edge-case, corruption, CLI, and Lean 4 kernel tests."""

    def test_wave10_whole_space_campaign_and_package_exports(self) -> None:
        import collatz_analysis as ca
        from collatz_analysis.cs_cegar_redteam import (
            audit_w10_front_a_srs_omit_r8_termination_and_labelled_syzygies,
            audit_w10_front_b_coprime_prime_divisor_law_mod24_and_laurent_6x6,
            audit_w10_front_c_stern_ocn_barrier_and_diamond7,
            audit_w10_front_d_dyadic_window_pinning_and_markov_mod54,
            load_witness_bank,
            run_wave10_whole_space_campaign,
            verify_witness_bank_ground_truth,
        )
        from collatz_analysis.formal_proofs import generate_full_proof_suite_report

        for exported_sym in (
            "stern_diatomic",
            "run_msb_one_counter_ocn",
            "is_diamond7_cone8",
            "cousin_diamond7_step_int",
            "cousin_diamond7_step_q6",
            "cousin_diamond7_block_return",
            "laurent_twobase_6x6_det_matrix",
            "laurent_twobase_6x6_det_closed",
            "audit_w10_front_a_srs_omit_r8_termination_and_labelled_syzygies",
            "audit_w10_front_b_coprime_prime_divisor_law_mod24_and_laurent_6x6",
            "audit_w10_front_c_stern_ocn_barrier_and_diamond7",
            "audit_w10_front_d_dyadic_window_pinning_and_markov_mod54",
            "run_wave10_whole_space_campaign",
        ):
            self.assertTrue(hasattr(ca, exported_sym), f"Missing package export: {exported_sym}")

        bank = load_witness_bank()
        self.assertGreaterEqual(len(bank["domains"]["z_pos_high_glide"]), 30)
        self.assertGreaterEqual(len(bank["domains"]["m1_q2_pos"]), 16)
        self.assertGreaterEqual(len(bank["domains"]["m2_z_neg"]), 4)
        self.assertGreaterEqual(len(bank["domains"]["m3_supercritical"]), 10)
        self.assertGreaterEqual(len(bank["domains"]["log2_3_convergents"]), 15)
        self.assertGreaterEqual(sum(len(v) for v in bank["domains"].values()), 75)
        self.assertGreaterEqual(len(bank["falsified_hypotheses"]), 32)
        hyp_ids = {h["hypothesis_id"] for h in bank["falsified_hypotheses"]}
        for hid in (
            "W10_H1_STERN_BROCOT_2REGULAR_AND_ONE_COUNTER_OCN_PREIMAGE_WEIGHTS",
            "W10_H2_LABELLED_PARIKH_TOWERS_ON_SWAPS_AND_OMEGA4_DIAMOND7_BARRIER",
            "W10_H3_TWOBASE_6X6_ODD_U_NONVANISHING_AND_MOD24_11_13_COPRIME_PRIMES",
            "W10_H4_WEIGHT_BLIND_DYADIC_WINDOW_SHIFT_PINNING",
        ):
            self.assertIn(hid, hyp_ids)

        truth = verify_witness_bank_ground_truth()
        self.assertTrue(truth["all_witnesses_ground_truth_verified"])
        self.assertGreaterEqual(truth["verified_witness_count"], 75)
        self.assertEqual(truth["failed_witness_ids"], ())

        w10 = run_wave10_whole_space_campaign()
        self.assertTrue(w10["passed"])
        self.assertEqual(w10["verdict"], "REDTEAM-PASSED")
        self.assertTrue(w10["universality_gate_passed"])
        self.assertGreaterEqual(w10["witness_bank_total_entries"], 75)
        self.assertGreaterEqual(w10["witness_bank_falsified_count"], 32)

        fa = audit_w10_front_a_srs_omit_r8_termination_and_labelled_syzygies()
        self.assertTrue(fa["fixed_point_swap_preservation_verified"])
        self.assertTrue(fa["m3_s9_2level_1d_and_all11_goe_removal_verified"])
        self.assertTrue(fa["twosided_l2_r2_omit_r8_14_and_omit_r3_4_removal_verified"])
        self.assertTrue(fa["twosided_l2_r6_omit_r8_2level_termination_verified"])
        self.assertTrue(fa["labelled_parikh_syzygy_barriers_verified"])

        fb = audit_w10_front_b_coprime_prime_divisor_law_mod24_and_laurent_6x6()
        self.assertTrue(fb["coprime_order_lagrange_and_mod24_reciprocity_verified"])
        self.assertTrue(fb["two_block_shared_mersenne_mod24_and_r2_squeeze_verified"])
        self.assertTrue(fb["laurent_6x6_single_base_t5u1_verified"])
        self.assertTrue(fb["laurent_6x6_single_base_t2u3_and_confluent_extrapolation_verified"])
        self.assertTrue(fb["laurent_6x6_twobase_closed_form_and_cone_verified"])
        self.assertTrue(fb["laurent_6x6_exact_zero_locus_and_u1_u2_flips_verified"])

        fc = audit_w10_front_c_stern_ocn_barrier_and_diamond7()
        self.assertTrue(fc["stern_brocot_2regular_spines_verified"])
        self.assertTrue(fc["stern_alternating_01_fib_and_zero_excess_ocn_verified"])
        self.assertTrue(fc["one_counter_ocn_pumping_dichotomy_verified"])
        self.assertTrue(fc["cousin_diamond7_outside_cones45678_descent_verified"])
        self.assertTrue(fc["cousin_diamond7_cone8_5tier_cascade_verified"])
        self.assertTrue(fc["cousin_diamond7_countermodels_verified"])

        fd = audit_w10_front_d_dyadic_window_pinning_and_markov_mod54()
        self.assertTrue(fd["markov_mod54_bijection_and_27_lock_verified"])
        self.assertTrue(fd["dyadic_window_envelope_and_unique_shift_pinning_verified"])
        self.assertTrue(fd["dyadic_window_occupancy_and_diagonal_l2_energy_verified"])

        suite_rep = generate_full_proof_suite_report()
        self.assertIn("wave10_whole_space_campaign", suite_rep)
        self.assertTrue(suite_rep["wave10_whole_space_campaign"]["passed"])

    def test_wave10_edge_cases_error_paths_and_witness_corruption(self) -> None:
        import copy
        from fractions import Fraction
        from itertools import product
        import json
        import tempfile
        from collatz_analysis.cs_cegar_redteam import (
            _dynamic_pred_mod24_11_13_prime_admits_coprime_orders,
            _dynamic_pred_phi2_on_cousin_diamond7_outside_cones4567,
            _dynamic_pred_stern_or_q1_ocn_separates_preimages,
            _dynamic_pred_twobase_6x6_odd_u_nonzero_and_u2_cone_pos,
            _dynamic_pred_weight_blind_dyadic_window_shift_pinning,
            cousin_diamond2_phi,
            cousin_diamond6_step_q6,
            cousin_diamond7_block_return,
            cousin_diamond7_step_int,
            cousin_diamond7_step_q6,
            evaluate_hypothesis_against_witness_bank,
            is_diamond6_cone7,
            is_diamond7_cone8,
            laurent_twobase_6x6_det_closed,
            laurent_twobase_6x6_det_matrix,
            load_witness_bank,
            run_msb_one_counter_ocn,
            stern_diatomic,
            verify_witness_bank_ground_truth,
        )

        # Boundary checks for 2-regular Stern-Brocot diatomic sequence
        for n_val, exp_stern in (
            (0, 0), (1, 1), (2, 1), (3, 2), (4, 1), (5, 3), (6, 2),
            (37, 11), (56, 3), (112, 3), (224, 3),
        ):
            self.assertEqual(stern_diatomic(n_val), exp_stern)

        # Boundary & non-regularity checks for 1-counter pushdown OCN
        # Dyck OCN: push on 1 (dz[1]=1, dp[1]=1), pop on 0 when c>0 (dz[0]=0, dp[0]=-1)
        self.assertEqual(run_msb_one_counter_ocn(1, [(0, 1)], [(-1, 1)], 0, 1), (0, 1))
        self.assertEqual(run_msb_one_counter_ocn(1, [(0, 1)], [(-1, 1)], 0, 1, c0=3), (0, 4))
        self.assertEqual(run_msb_one_counter_ocn(1, [((0, 0), (0, 1))], [((0, -1), (0, 1))], 0, 56), (0, 0))
        self.assertEqual(run_msb_one_counter_ocn(1, [(0, 1)], [(-1, 1)], 0, 112), (0, 0))
        # Reverse-Dyck OCN (inc on 1 when c==0, dec on 0 when c>0, inc on 0 when c==0): separates 56 vs 112!
        self.assertNotEqual(
            run_msb_one_counter_ocn(1, [(1, 1)], [(-1, 1)], 0, 56)[1] == 0,
            run_msb_one_counter_ocn(1, [(1, 1)], [(-1, 1)], 0, 112)[1] == 0,
        )
        # Yet ALL 36 Q = 1 OCNs lock (c == 0) identically on 56 vs 224 = 4 * 56!
        for dz0, dz1 in product((0, 1), repeat=2):
            for dp0, dp1 in product((-1, 0, 1), repeat=2):
                c56 = run_msb_one_counter_ocn(1, [(dz0, dz1)], [(dp0, dp1)], 0, 56)[1]
                c224 = run_msb_one_counter_ocn(1, [(dz0, dz1)], [(dp0, dp1)], 0, 224)[1]
                self.assertEqual(c56 == 0, c224 == 0)

        # Boundary, resonant-zero, sign-flip, & convergent-cone checks for 6x6 two-base Laurent determinants
        for w_e, k_e, u_e in ((0, 0, 1), (0, 5, 2), (5, 0, 2), (9, 16, 1), (27, 64, 2)):
            self.assertEqual(
                laurent_twobase_6x6_det_matrix(w_e, k_e, u_e),
                laurent_twobase_6x6_det_closed(w_e, k_e, u_e),
            )
        self.assertEqual(laurent_twobase_6x6_det_matrix(9, 16, 1), 0)
        self.assertEqual(laurent_twobase_6x6_det_matrix(27, 64, 2), 0)
        self.assertEqual(laurent_twobase_6x6_det_closed(243, 832, 3), 0)
        self.assertGreater(laurent_twobase_6x6_det_matrix(2, 3, 1), 0)
        self.assertLess(laurent_twobase_6x6_det_matrix(5, 8, 1), 0)
        self.assertLess(laurent_twobase_6x6_det_matrix(3, 5, 2), 0)
        self.assertGreater(laurent_twobase_6x6_det_matrix(5, 8, 2), 0)
        for w_c, k_c in ((1, 1), (3, 5), (5, 8), (12, 19)):
            self.assertGreater(laurent_twobase_6x6_det_matrix(w_c, k_c, 3), 0)

        # Boundary & 5-tier cascade checks for T_diamond7 and Cone 8
        self.assertFalse(is_diamond7_cone8(4_159_701))             # < 12548309
        self.assertFalse(is_diamond7_cone8(12_548_308))            # < 12548309
        self.assertTrue(is_diamond7_cone8(12_548_309))             # 2^22 * 3 - 34603 (minimal Cone 8)
        self.assertFalse(is_diamond7_cone8((1 << 22) * 15 - 34_603))  # coprime23 == 5 != 1
        self.assertEqual(cousin_diamond7_step_int(12_548_309), 294_101)
        self.assertEqual(cousin_diamond7_step_int(294_101), 6_893)
        self.assertEqual(cousin_diamond7_step_int(6_893), 2_585)
        self.assertEqual(cousin_diamond7_block_return(1), (0, 1))
        self.assertEqual(cousin_diamond7_block_return(2), (1, 1))
        self.assertEqual(cousin_diamond7_block_return(3), (1, 5))
        self.assertEqual(cousin_diamond7_block_return(12_548_309), (14, 1))
        x_jump8 = 3 * (1 << 113) - 34_603
        y_jump8 = cousin_diamond7_step_int(x_jump8)
        self.assertTrue(is_diamond7_cone8(x_jump8))
        self.assertTrue(is_diamond6_cone7(y_jump8))
        self.assertGreater(cousin_diamond2_phi(y_jump8), cousin_diamond2_phi(x_jump8))
        self.assertEqual(cousin_diamond7_block_return(x_jump8), (104, 1))

        # Non-integer Q_(6)^+ rationals (including 12548309/7) ALWAYS bypass Cone 8
        for den in (5, 7, 11, 13):
            for num in (1, 19, 294_101, 12_548_309, 12_548_309 * den - 34_603 * den + 1):
                f_q6 = Fraction(num, den)
                if f_q6.denominator > 1:
                    self.assertEqual(
                        cousin_diamond7_step_q6(f_q6),
                        cousin_diamond6_step_q6(f_q6),
                    )

        # Error-path validation across all Wave 10 primitives
        for bad_n in (-1, True, False, 1.5, "56"):
            with self.assertRaises(ValueError):
                stern_diatomic(bad_n)  # type: ignore[arg-type]

        for bad_q in (0, -1, True, False, 1.5, "1"):
            with self.assertRaises(ValueError):
                run_msb_one_counter_ocn(bad_q, [(0, 0)], [(0, 0)], 0, 5)  # type: ignore[arg-type]
        for bad_q0 in (-1, 1, True, False, "0"):
            with self.assertRaises(ValueError):
                run_msb_one_counter_ocn(1, [(0, 0)], [(0, 0)], bad_q0, 5)  # type: ignore[arg-type]
        for bad_n_ocn in (0, -2, True, False, 2.5, "56"):
            with self.assertRaises(ValueError):
                run_msb_one_counter_ocn(1, [(0, 0)], [(0, 0)], 0, bad_n_ocn)  # type: ignore[arg-type]
        for bad_c0 in (-1, True, False, 1.5, "0"):
            with self.assertRaises(ValueError):
                run_msb_one_counter_ocn(1, [(0, 0)], [(0, 0)], 0, 5, c0=bad_c0)  # type: ignore[arg-type]
        for bad_dz in ([], [(0,)], [(-1, 0)], [(0, 2)], [(0, True)], [((1, 0), (0, 0))]):
            with self.assertRaises(ValueError):
                run_msb_one_counter_ocn(1, bad_dz, [(0, 0)], 0, 5)  # type: ignore[arg-type]
        for bad_dp in ([], [(0,)], [(-2, 0)], [(0, 2)], [(0, True)], [((1, 0), (0, 0))]):
            with self.assertRaises(ValueError):
                run_msb_one_counter_ocn(1, [(0, 0)], bad_dp, 0, 5)  # type: ignore[arg-type]
        with self.assertRaises(ValueError):
            run_msb_one_counter_ocn(2, [(0, 0), (0, 0)], [(0, 0), (0, 0)], 0, 5)  # Q=2 needs (q, dc) tuples

        for det_fn in (laurent_twobase_6x6_det_matrix, laurent_twobase_6x6_det_closed):
            for bad_args in ((-1, 2, 1), (2, -1, 1), (2, 3, 0), (True, 3, 1), (2, 3, False), (2.5, 3, 1)):
                with self.assertRaises(ValueError):
                    det_fn(*bad_args)  # type: ignore[arg-type]

        for bad_x in (True, False, 2.5, "12548309"):
            with self.assertRaises(ValueError):
                is_diamond7_cone8(bad_x)  # type: ignore[arg-type]
            with self.assertRaises(ValueError):
                cousin_diamond7_step_int(bad_x)  # type: ignore[arg-type]
            with self.assertRaises(ValueError):
                cousin_diamond7_step_q6(bad_x)  # type: ignore[arg-type]
        for bad_mul in (1, 2, 4, -3, True):
            with self.assertRaises(ValueError):
                cousin_diamond7_step_int(7, q=bad_mul)  # type: ignore[arg-type]
        for bad_pos in (0, -1, True):
            with self.assertRaises(ValueError):
                cousin_diamond7_block_return(bad_pos)  # type: ignore[arg-type]
        for bad_frac in (Fraction(1, 2), Fraction(1, 3), Fraction(5, 6)):
            with self.assertRaises(ValueError):
                cousin_diamond7_step_q6(bad_frac)

        # Synthetic witness-bank check on all 5 Wave 10 dynamic predicates (proving zero hardcoded IDs)
        base_bank = load_witness_bank()
        with tempfile.TemporaryDirectory() as tmpdir:
            synth_bank = copy.deepcopy(base_bank)
            synth_bank["falsified_hypotheses"] = []
            synth_bank["domains"]["z_pos_high_glide"] = [
                {
                    "witness_id": "SYNTH_STERN_OCN_800_VS_3200",
                    "seed": 533,
                    "next_compressed": 800,  # 800 % 3 == 2; all 36 Q=1 OCNs lock (c==0) on 800 vs 3200!
                    "ocn_q1_multi_even_preimage": 3200,
                    "kills_mechanisms": ["stern_ocn"],
                },
                {
                    "witness_id": "SYNTH_D7_CONE8_K275_M1",
                    "seed": 3 * (1 << 275) - 34_603,  # 275 = 113 + 162: 3^5 | (2^274 - 5767) jumps Phi_2 upward
                    "kills_mechanisms": ["phi2_on_diamond7"],
                },
                {
                    "witness_id": "SYNTH_DYADIC_M10_L8_SPLIT_1205_VS_1613",
                    "seed": 1205,
                    "core_word": [1, 0, 0, 0, 0, 1, 0, 1],
                    "dyadic_window_exp_m": 10,
                    "dyadic_partner_core_word": [1, 0, 0, 1, 0, 0, 1, 1],
                    "kills_mechanisms": ["weight_blind_dyadic"],
                },
            ]
            synth_bank["domains"]["log2_3_convergents"] = [
                {
                    "witness_id": "SYNTH_TWOBASE_6X6_W243_K832_U3",
                    "W": 243,
                    "K": 832,
                    "gap_sign": 1,
                    "laurent_twobase_6x6_u": 3,  # odd u = 3: 8 * 728 * 243 == 27 * 63 * 832
                    "kills_mechanisms": ["twobase_6x6_odd_u"],
                },
                {
                    "witness_id": "SYNTH_MOD24_11_PRIME_59",
                    "W": 5,
                    "K": 8,
                    "gap_sign": 1,
                    "mod24_excluded_prime": 59,  # 59 % 24 == 11
                    "kills_mechanisms": ["mod24_coprime"],
                },
            ]
            synth_p = Path(tmpdir) / "synth_w10.json"
            synth_p.write_text(json.dumps(synth_bank), encoding="utf-8")

            g1 = evaluate_hypothesis_against_witness_bank(
                "SynthSternOCN", _dynamic_pred_stern_or_q1_ocn_separates_preimages,
                domains=("z_pos_high_glide",), bank_path=synth_p,
            )
            self.assertEqual(g1["minimal_failure"], ("z_pos_high_glide", "SYNTH_STERN_OCN_800_VS_3200"))
            g2 = evaluate_hypothesis_against_witness_bank(
                "SynthD7", _dynamic_pred_phi2_on_cousin_diamond7_outside_cones4567,
                domains=("z_pos_high_glide",), bank_path=synth_p,
            )
            self.assertEqual(g2["minimal_failure"], ("z_pos_high_glide", "SYNTH_D7_CONE8_K275_M1"))
            g3 = evaluate_hypothesis_against_witness_bank(
                "SynthTwoBase6x6", _dynamic_pred_twobase_6x6_odd_u_nonzero_and_u2_cone_pos,
                domains=("log2_3_convergents",), bank_path=synth_p,
            )
            self.assertEqual(g3["minimal_failure"], ("log2_3_convergents", "SYNTH_TWOBASE_6X6_W243_K832_U3"))
            g4 = evaluate_hypothesis_against_witness_bank(
                "SynthMod24", _dynamic_pred_mod24_11_13_prime_admits_coprime_orders,
                domains=("log2_3_convergents",), bank_path=synth_p,
            )
            self.assertEqual(g4["minimal_failure"], ("log2_3_convergents", "SYNTH_MOD24_11_PRIME_59"))
            g5 = evaluate_hypothesis_against_witness_bank(
                "SynthDyadicPin", _dynamic_pred_weight_blind_dyadic_window_shift_pinning,
                domains=("z_pos_high_glide",), bank_path=synth_p,
            )
            self.assertEqual(g5["minimal_failure"], ("z_pos_high_glide", "SYNTH_DYADIC_M10_L8_SPLIT_1205_VS_1613"))

            # Verify primary ground-truth corruption detection across all 7 new Wave 10 witnesses
            corruptions = [
                ("z_pos_high_glide", "ZPOS_STERN_AND_OCN_PREIMAGE_COLLAPSE_56_VS_224", "stern_seed", 10),
                ("z_pos_high_glide", "ZPOS_COUSIN_DIAMOND7_CONE8_JUMP", "cousin_diamond7_steps_to_1", 103),
                ("z_pos_high_glide", "ZPOS_DYADIC_WINDOW_M8_L6_WEIGHT_SPLIT_301_VS_403", "dyadic_partner_seed", 405),
                ("m1_q2_pos", "M1_COUSIN_DIAMOND7_1_OVER_7", "orbit", ["1/7", "5/7", "11/7", "20/7", "3/7"]),
                ("m3_supercritical", "M3_COUSIN_DIAMOND7_7X1_CYCLE5", "orbit", [5, 18, 9, 32, 11]),
                ("log2_3_convergents", "LAURENT_TWOBASE_6X6_ODD_U1_ZERO_9_16_AND_U2_CONE_FLIP", "laurent_twobase_6x6_det", 1),
                ("log2_3_convergents", "COPRIME_PRIME_MOD24_11_13_RECIPROCITY_EXCLUSION_D13", "mod24_ord32", 6),
            ]
            bad_b = copy.deepcopy(base_bank)
            for dom, wid, field, bad_val in corruptions:
                for item in bad_b["domains"][dom]:
                    if item["witness_id"] == wid:
                        item[field] = bad_val
            bad_p = Path(tmpdir) / "corrupt_w10_all7.json"
            bad_p.write_text(json.dumps(bad_b), encoding="utf-8")
            chk = verify_witness_bank_ground_truth(bad_p)
            self.assertFalse(chk["all_witnesses_ground_truth_verified"])
            for _, wid, _, _ in corruptions:
                self.assertIn(wid, chk["failed_witness_ids"], f"Missed corruption on {wid}")

            # Verify subtle secondary-field corruptions on Wave 10 witnesses
            subtle_corruptions = [
                ("z_pos_high_glide", "ZPOS_STERN_AND_OCN_PREIMAGE_COLLAPSE_56_VS_224", "ocn_q1_multi_even_preimage", 112),
                ("z_pos_high_glide", "ZPOS_COUSIN_DIAMOND7_CONE8_JUMP", "cousin_diamond7_next", 294101),
                ("z_pos_high_glide", "ZPOS_DYADIC_WINDOW_M8_L6_WEIGHT_SPLIT_301_VS_403", "dyadic_window_exp_m", 9),
                ("log2_3_convergents", "LAURENT_TWOBASE_6X6_ODD_U1_ZERO_9_16_AND_U2_CONE_FLIP", "cone_flip_u2_neg_pair", [5, 8]),
                ("log2_3_convergents", "COPRIME_PRIME_MOD24_11_13_RECIPROCITY_EXCLUSION_D13", "mod24_companion_ord2", 5),
            ]
            bad_b2 = copy.deepcopy(base_bank)
            for dom, wid, field, bad_val in subtle_corruptions:
                for item in bad_b2["domains"][dom]:
                    if item["witness_id"] == wid:
                        item[field] = bad_val
            bad_p2 = Path(tmpdir) / "corrupt_w10_subtle.json"
            bad_p2.write_text(json.dumps(bad_b2), encoding="utf-8")
            chk2 = verify_witness_bank_ground_truth(bad_p2)
            self.assertFalse(chk2["all_witnesses_ground_truth_verified"])
            for _, wid, _, _ in subtle_corruptions:
                self.assertIn(wid, chk2["failed_witness_ids"], f"Missed subtle corruption on {wid}")

    def test_wave10_lean4_zero_custom_axioms_docstring_and_pii_audit(self) -> None:
        import re
        from collatz_analysis.formal_proofs import (
            ALLOWED_LEAN4_FOUNDATIONAL_AXIOMS,
            verify_lean4_kernel_proofs,
        )

        pkg_dir = Path(__file__).resolve().parent.parent
        res = verify_lean4_kernel_proofs()
        self.assertTrue(res["pure_kernel_verified"])
        self.assertTrue(res["zero_sorry_verified"])
        self.assertTrue(res["zero_warnings_verified"])
        self.assertGreaterEqual(len(res["lean_files"]), 59)
        self.assertGreaterEqual(res["theorems_audited"], 2129)
        self.assertGreaterEqual(res["axiom_free_theorem_count"], 599)
        self.assertTrue(any(Path(p).name == "Wave10WholeSpace.lean" for p in res["lean_files"]))

        ax_map = res["axioms_by_theorem"]
        w10_theorems = (
            "zantema_fixed_point_swap_commutators",
            "collatz_l2_is_exact_left_semantic_model",
            "two_sided_zantema_semantic_labelling_soundness",
            "s9_mod3_2level_termination_and_all11_goe_removal_cert",
            "omit_r8_twosided_mod6_admits_2d_hw_tower",
            "omit_r8_10_of_11_unlabelled_terminates",
            "positive_parikh_syzygy_blocks_all_omega_towers",
            "labelled_swap_parikh_syzygy_barriers",
            "labelled_swap_parikh_syzygy_barriers_complete",
            "natProdRange_inj_eq_fact",
            "fermat_little_mod_prime",
            "exists_exact_mult_order_mod_prime",
            "coprime_dvd_of_dvd_mul_aux",
            "one_block_all_prime_divisors_coprime_order_and_totient",
            "gauss_lemma_mod_prime",
            "mod24_11_13_quadratic_reciprocity_and_one_block_exclusion",
            "squeeze46_up_to_40_cert",
            "two_block_shared_mersenne_mod24_and_even_order_obstructions",
            "laurent_6x6_exact_factorization_and_zero_locus",
            "laurent_6x6_single_base_t5u1_and_confluent_extrapolation",
            "stern_brocot_2regular_preimage_impossibility",
            "stern_alternating_01_cascade_fib",
            "ocn_unary_zero_run_semilinear_dichotomy",
            "one_counter_ocn_preimage_impossibility",
            "zero_excess_ocn_and_zero_inc_preimage_impossibility",
            "cousinDiamond7StepInt_ofNat_eq",
            "cousin_diamond7_outside_cones45678_strict_descent",
            "not_cone8_six_mul_pow9_sub1",
            "cousin_diamond7_cones45678_exact_return",
            "cousin_diamond7_global_convergence",
            "cousin_diamond7_r_block_spiral_climb_and_laurent_impossibility",
            "cousin_diamond7_q6_noninteger_avoids_cone8",
            "cousin_diamond7_counter_model_separation",
            "markovShift_mod54_bijection_and_four_ones_27_lock",
            "affineCarry_add_pow2_le_pow3_mul_pow2",
            "dyadic_window_unique_shift_pinning_and_l2_energy",
        )
        for thm in w10_theorems:
            self.assertIn(thm, ax_map)
            self.assertTrue(
                set(ax_map[thm]).issubset(ALLOWED_LEAN4_FOUNDATIONAL_AXIOMS),
                f"Unexpected custom axiom in {thm}: {ax_map[thm]}",
            )

        for axfree_thm in (
            "collatzSemL2_lt",
            "evalCollatzSemL2_lt",
            "not_cone8_of_mod3_ne_2",
            "cousin_diamond7_counter_model_separation",
            "mem_filter_w10",
            "noDupNat_filter",
            "squeeze46_up_to_40_cert",
        ):
            self.assertEqual(ax_map[axfree_thm], [], f"Expected [] axioms on {axfree_thm}")

        for choice_free_thm in (
            "collatz_l2_is_exact_left_semantic_model",
            "s9_mod3_2level_termination_and_all11_goe_removal_cert",
            "omit_r8_twosided_mod6_admits_2d_hw_tower",
            "natProdRange_inj_eq_fact",
            "fermat_little_mod_prime",
            "exists_exact_mult_order_mod_prime",
            "coprime_dvd_of_dvd_mul_aux",
            "one_block_all_prime_divisors_coprime_order_and_totient",
            "laurent_6x6_exact_factorization_and_zero_locus",
            "stern_brocot_2regular_preimage_impossibility",
            "stern_alternating_01_cascade_fib",
            "ocn_unary_zero_run_semilinear_dichotomy",
            "cousin_diamond7_q6_noninteger_avoids_cone8",
            "affineCarry_add_pow2_le_pow3_mul_pow2",
        ):
            self.assertNotIn(
                "Classical.choice",
                ax_map[choice_free_thm],
                f"Expected choice-free proof on {choice_free_thm}",
            )

        w10_src = (pkg_dir / "CollatzFormal/Wave10WholeSpace.lean").read_text(encoding="utf-8")
        for doc, thm_name in re.findall(r"/--\s*(.*?)\s*-/\s*theorem\s+([A-Za-z0-9_']+)\b", w10_src, flags=re.S):
            if "`[]` axioms" in doc:
                self.assertEqual(ax_map.get(thm_name), [], f"False []-axiom docstring on {thm_name}")
            if "choice-free" in doc:
                self.assertNotIn("Classical.choice", ax_map.get(thm_name, []), f"False choice-free docstring on {thm_name}")

        axfree_claim_pats = (
            re.compile(r"`([A-Za-z0-9_']+)`\s*\(`\[\]`\s*axioms", flags=re.I),
            re.compile(r"`([A-Za-z0-9_']+)`\s*,\s*`\[\]`\s*axioms", flags=re.I),
        )
        for doc_rel in (
            "CollatzFormal/Wave10WholeSpace.lean",
            "PROOF_SPACE_LEDGER.md",
            "MATHEMATICAL_FINDINGS.md",
            "README.md",
        ):
            doc_txt = (pkg_dir / doc_rel).read_text(encoding="utf-8")
            for pat in axfree_claim_pats:
                for thm_ref in pat.findall(doc_txt):
                    self.assertEqual(
                        ax_map.get(thm_ref),
                        [],
                        f"False []-axiom claim in {doc_rel} on {thm_ref}: {ax_map.get(thm_ref)}",
                    )
        self.assertNotIn("(`[]` Axioms)", w10_src)

        # Repo-wide zero-PII / machine-path hygiene scan across tracked source & docs
        forbidden_tokens = (
            "Us" + "ers" + "\\",
            "Us" + "ers/",
            "/" + "home" + "/",
            "C:" + "\\",
            "C:" + "/",
        )
        for path in sorted(pkg_dir.rglob("*")):
            if ".lake" in path.parts or "__pycache__" in path.parts or path.is_dir():
                continue
            if path.suffix in {".py", ".lean", ".md", ".json", ".c"}:
                txt = path.read_text(encoding="utf-8")
                for tok in forbidden_tokens:
                    self.assertNotIn(tok, txt, f"Forbidden path token {tok!r} in {path.name}")

    def test_cli_summary_includes_wave10_loop_and_exit_gate(self) -> None:
        import contextlib
        import io
        from unittest import mock
        from collatz_analysis.cli import main as cli_main

        buf_sum = io.StringIO()
        with contextlib.redirect_stdout(buf_sum):
            rc_sum = cli_main(["--summary", "--dp-depth", "50"])
        self.assertEqual(rc_sum, 0)
        out = buf_sum.getvalue()
        self.assertIn("[Wave 10 Whole-Space Proof Loop]", out)
        self.assertIn("A=True, B=True", out)
        self.assertIn("C=True, T_diamond7=True, D=True", out)
        self.assertLess(
            out.index("[Wave 9 Whole-Space Proof Loop]"),
            out.index("[Wave 10 Whole-Space Proof Loop]"),
        )
        self.assertLess(
            out.index("[Wave 10 Whole-Space Proof Loop]"),
            out.index("[Lean 4 Kernel Verification]"),
        )

        failed_w10 = {
            "passed": False,
            "verdict": "FALSIFIED",
            "universality_gate_passed": True,
            "witness_bank_total_entries": 75,
            "witness_bank_falsified_count": 32,
            "witness_bank_ground_truth_verified": True,
            "front_a_srs_omit_r8_and_syzygies": {
                "fixed_point_swap_preservation_verified": True,
                "m3_s9_2level_1d_and_all11_goe_removal_verified": True,
                "twosided_l2_r2_omit_r8_14_and_omit_r3_4_removal_verified": True,
                "twosided_l2_r6_omit_r8_2level_termination_verified": False,
                "labelled_parikh_syzygy_barriers_verified": True,
            },
            "front_b_coprime_law_mod24_and_laurent_6x6": {
                "coprime_order_lagrange_and_mod24_reciprocity_verified": True,
                "two_block_shared_mersenne_mod24_and_r2_squeeze_verified": False,
                "laurent_6x6_single_base_t5u1_verified": True,
                "laurent_6x6_single_base_t2u3_and_confluent_extrapolation_verified": True,
                "laurent_6x6_twobase_closed_form_and_cone_verified": True,
                "laurent_6x6_exact_zero_locus_and_u1_u2_flips_verified": True,
            },
            "front_c_stern_ocn_and_diamond7": {
                "stern_brocot_2regular_spines_verified": True,
                "stern_alternating_01_fib_and_zero_excess_ocn_verified": False,
                "one_counter_ocn_pumping_dichotomy_verified": True,
                "cousin_diamond7_outside_cones45678_descent_verified": False,
                "cousin_diamond7_cone8_5tier_cascade_verified": True,
                "cousin_diamond7_countermodels_verified": True,
            },
            "front_d_dyadic_window_and_markov_mod54": {
                "markov_mod54_bijection_and_27_lock_verified": False,
                "dyadic_window_envelope_and_unique_shift_pinning_verified": True,
                "dyadic_window_occupancy_and_diagonal_l2_energy_verified": True,
            },
        }
        buf_fail = io.StringIO()
        with mock.patch(
            "collatz_analysis.cs_cegar_redteam.run_wave10_whole_space_campaign",
            return_value=failed_w10,
        ), mock.patch(
            "collatz_analysis.cli.verify_lean4_kernel_proofs",
            return_value={"lean_available": False, "static_hygiene_clean": True},
        ), contextlib.redirect_stdout(buf_fail):
            rc_fail = cli_main(["--summary", "--dp-depth", "10"])
        self.assertEqual(rc_fail, 1)
        self.assertIn("A=False, B=False", buf_fail.getvalue())
        self.assertIn("T_diamond7=False, D=False", buf_fail.getvalue())


class TestWave11WholeSpaceCampaign(unittest.TestCase):
    """End-to-end verification of Wave 11 whole-space red-team, Lean 4 kernel, & CLI gates."""

    def test_wave11_whole_space_campaign_and_witness_bank(self) -> None:
        import collatz_analysis as ca
        from collatz_analysis.cs_cegar_redteam import (
            audit_w11_front_a_left_anchored_dp_and_mersenne_r8_barrier,
            audit_w11_front_b_reciprocity_sylow_and_laurent_t3u2,
            audit_w11_front_c_general_mixed_sign_ocn_and_diamond8,
            audit_w11_front_d_supercritical_dyadic_and_markov_mod162,
            load_witness_bank,
            run_wave11_whole_space_campaign,
            verify_witness_bank_ground_truth,
        )
        from collatz_analysis.formal_proofs import generate_full_proof_suite_report

        for exported_sym in (
            "run_lsb_one_counter_ocn",
            "run_msb_pda_stack",
            "mod9_backward_collatz_branch_next",
            "is_diamond8_cone9",
            "cousin_diamond8_step_int",
            "cousin_diamond8_step_q6",
            "cousin_diamond8_block_return",
            "laurent_twobase_6x6_t3u2_det_matrix",
            "laurent_twobase_6x6_t3u2_det_closed",
            "laurent_twobase_8x8_t4u2_det_matrix",
            "audit_w11_front_a_left_anchored_dp_and_mersenne_r8_barrier",
            "audit_w11_front_b_reciprocity_sylow_and_laurent_t3u2",
            "audit_w11_front_c_general_mixed_sign_ocn_and_diamond8",
            "audit_w11_front_d_supercritical_dyadic_and_markov_mod162",
            "run_wave11_whole_space_campaign",
        ):
            self.assertTrue(hasattr(ca, exported_sym), f"Missing package export: {exported_sym}")

        bank = load_witness_bank()
        self.assertEqual(len(bank["domains"]["z_pos_high_glide"]), 35)
        self.assertEqual(len(bank["domains"]["m1_q2_pos"]), 17)
        self.assertEqual(len(bank["domains"]["m2_z_neg"]), 4)
        self.assertEqual(len(bank["domains"]["m3_supercritical"]), 11)
        self.assertEqual(len(bank["domains"]["log2_3_convergents"]), 18)
        self.assertEqual(sum(len(v) for v in bank["domains"].values()), 85)
        self.assertEqual(len(bank["falsified_hypotheses"]), 36)
        hyp_ids = {h["hypothesis_id"] for h in bank["falsified_hypotheses"]}
        for hid in (
            "W11_H1_GENERAL_MIXED_SIGN_OCN_MODE_AND_SLOPE_PREIMAGE_WEIGHTS",
            "W11_H2_FINITE_LEFT_RIGHT_CARRIER_MERSENNE_R8_AND_OMEGA5_DIAMOND8_BARRIER",
            "W11_H3_TWOBASE_6X6_T3U2_EVEN_U_NONVANISHING_AND_MOD24_5_17_EVEN_GCD",
            "W11_H4_LENGTH_BLIND_DYADIC_SHIFT_PINNING_AND_SUBCRITICAL_LENGTH_CEILING",
        ):
            self.assertIn(hid, hyp_ids)

        truth = verify_witness_bank_ground_truth()
        self.assertTrue(truth["all_witnesses_ground_truth_verified"])
        self.assertEqual(truth["verified_witness_count"], 85)
        self.assertEqual(truth["failed_witness_ids"], ())

        w11 = run_wave11_whole_space_campaign()
        self.assertTrue(w11["passed"])
        self.assertEqual(w11["verdict"], "REDTEAM-PASSED")
        self.assertTrue(w11["universality_gate_passed"])
        self.assertEqual(w11["witness_bank_total_entries"], 85)
        self.assertEqual(w11["witness_bank_falsified_count"], 36)

        fa = audit_w11_front_a_left_anchored_dp_and_mersenne_r8_barrier()
        self.assertTrue(fa["left_anchored_dp_and_omit_r2_termination_verified"])
        self.assertTrue(fa["twosided_m3_m6_omit_r3_and_all11_cascades_verified"])
        self.assertTrue(fa["universal_mersenne_b1_t2_lock_and_r8_cycle_verified"])
        self.assertTrue(fa["higher_carriers_k2_4_8_m6_12_18_and_flip2_verified"])

        fb = audit_w11_front_b_reciprocity_sylow_and_laurent_t3u2()
        self.assertTrue(fb["reciprocity_mod24_complete_and_sylow_verified"])
        self.assertTrue(fb["twoblock_cubic_quintic_octic_floors_verified"])
        self.assertTrue(fb["companion_quotient_cascades_and_mblock_sylow_verified"])
        self.assertTrue(fb["confluent_t2_t3_extrapolation_8x8_and_laplace_verified"])
        self.assertTrue(fb["laurent_8x8_twobase_t4u2_divisibility_and_cone_flip_verified"])
        self.assertTrue(fb["laurent_6x6_t3u2_closed_form_odd_u_and_cone_pos_verified"])

        fc = audit_w11_front_c_general_mixed_sign_ocn_and_diamond8()
        self.assertTrue(fc["general_mixed_sign_ocn_mode_and_dual_pumping_verified"])
        self.assertTrue(fc["lsb_raw_counter_ocn_and_pda_two_counter_verified"])
        self.assertTrue(fc["all_ocn_raw_counter_and_mod9_branch_descent_verified"])
        self.assertTrue(fc["cousin_diamond8_outside_cones4to9_descent_verified"])
        self.assertTrue(fc["cousin_diamond8_cone9_6tier_cascade_verified"])
        self.assertTrue(fc["cousin_diamond8_countermodels_verified"])

        fd = audit_w11_front_d_supercritical_dyadic_and_markov_mod162()
        self.assertTrue(fd["first_hit_shift_ge3_and_pow3_ones_verified"])
        self.assertTrue(fd["markov_mod162_bijection_and_81_lock_verified"])
        self.assertTrue(fd["dyadic_supercritical_shift_multiplicity_verified"])
        self.assertTrue(fd["surviving_window_leaves_mod162_and_fiber_equidist_verified"])

        suite_rep = generate_full_proof_suite_report()
        self.assertIn("wave11_whole_space_campaign", suite_rep)
        self.assertTrue(suite_rep["wave11_whole_space_campaign"]["passed"])

    def test_wave11_edge_cases_error_paths_and_witness_corruption(self) -> None:
        import copy
        from fractions import Fraction
        import json
        import tempfile
        from collatz_analysis.cs_cegar_redteam import (
            _canonical_pda_q2_g3_table,
            _dynamic_pred_asym_slope_q2_ocn_mersenne_bypass_weight,
            _dynamic_pred_length_blind_dyadic_shift_pinning_or_subcritical,
            _dynamic_pred_mixed_sign_q2_ocn_mode_separates_preimages,
            _dynamic_pred_mod24_5_17_prime_forces_even_gcd,
            _dynamic_pred_pda_q2_g3_stack_separates_preimages,
            _dynamic_pred_phi2_on_cousin_diamond8_outside_cones4to8,
            _dynamic_pred_twobase_6x6_t3u2_even_u_nonzero_and_all_pos,
            _dynamic_pred_twobase_8x8_t4u2_cone_positivity,
            cousin_diamond2_phi,
            cousin_diamond7_step_q6,
            cousin_diamond8_block_return,
            cousin_diamond8_step_int,
            cousin_diamond8_step_q6,
            evaluate_hypothesis_against_witness_bank,
            is_diamond7_cone8,
            is_diamond8_cone9,
            laurent_twobase_6x6_t3u2_det_closed,
            laurent_twobase_6x6_t3u2_det_matrix,
            laurent_twobase_8x8_t4u2_det_matrix,
            load_witness_bank,
            mod9_backward_collatz_branch_next,
            run_lsb_one_counter_ocn,
            run_msb_one_counter_ocn,
            run_msb_pda_stack,
            verify_witness_bank_ground_truth,
        )

        # Mixed-sign Q = 2 OCN boundary checks (separates 56 vs 224, yet collapses 12416 vs 49664)
        dz_mix = [((1, 0), (0, 1)), ((0, 0), (1, 1))]
        dp_mix = [((1, 0), (0, 1)), ((0, -1), (1, -1))]
        self.assertEqual(run_msb_one_counter_ocn(2, dz_mix, dp_mix, 0, 56)[1], 2)
        self.assertEqual(run_msb_one_counter_ocn(2, dz_mix, dp_mix, 0, 224)[1], 1)
        self.assertEqual(run_msb_one_counter_ocn(2, dz_mix, dp_mix, 0, 12_416), (1, 0))
        self.assertEqual(run_msb_one_counter_ocn(2, dz_mix, dp_mix, 0, 49_664), (1, 0))
        self.assertEqual(run_lsb_one_counter_ocn(1, [(0, 1)], [(-1, 1)], 0, 1), (0, 1))
        self.assertEqual(run_lsb_one_counter_ocn(1, [(0, 1)], [(-1, 1)], 0, 1, c0=2), (0, 3))
        self.assertEqual(
            run_lsb_one_counter_ocn(2, dz_mix, dp_mix, 0, 12_416)[0],
            run_lsb_one_counter_ocn(2, dz_mix, dp_mix, 0, 49_664)[0],
        )

        # Boundary, odd-u non-vanishing, all-u cone positivity, & even-u resonant-zero checks on T3U2 6x6
        for w_e, k_e, u_e in ((0, 0, 1), (0, 5, 2), (5, 0, 2), (1, 1, 1), (1, 2, 1), (3, 8, 2), (9, 16, 1)):
            self.assertEqual(
                laurent_twobase_6x6_t3u2_det_matrix(w_e, k_e, u_e),
                laurent_twobase_6x6_t3u2_det_closed(w_e, k_e, u_e),
            )
        self.assertEqual(laurent_twobase_6x6_t3u2_det_matrix(3, 8, 2), 0)
        self.assertEqual(laurent_twobase_6x6_t3u2_det_matrix(1, 2, 1), -96)
        self.assertEqual(laurent_twobase_6x6_t3u2_det_matrix(2, 3, 1), -675)  # 3^2 > 2^3 (sharpness of 3^W < 2^K)
        self.assertEqual(laurent_twobase_6x6_t3u2_det_matrix(12, 19, 1), -165_699)  # 3^12 > 2^19 (sharpness of 3^W < 2^K)
        self.assertNotEqual(laurent_twobase_6x6_t3u2_det_matrix(9, 16, 1), 0)
        for u_c in (1, 2, 3, 4):
            for w_c, k_c in ((3, 5), (5, 8), (17, 27), (41, 65), (306, 485)):
                self.assertGreater(laurent_twobase_6x6_t3u2_det_closed(w_c, k_c, u_c), 0)

        # Boundary & cone sign-flip checks on 8x8 two-base T4U2 & multi-symbol context-free PDA stack
        self.assertEqual(laurent_twobase_8x8_t4u2_det_matrix(0, 0, 1), 0)
        self.assertEqual(laurent_twobase_8x8_t4u2_det_matrix(3, 5, 1), -559_794_375)
        self.assertEqual(laurent_twobase_8x8_t4u2_det_matrix(3, 5, 4), -20_487_059_690_701_585_693_359_375)
        self.assertGreater(laurent_twobase_8x8_t4u2_det_matrix(5, 8, 4), 0)

        pda_tbl = _canonical_pda_q2_g3_table()
        self.assertEqual(run_msb_pda_stack(2, 3, pda_tbl, 0, 1), (1, 1, 1))
        self.assertEqual(run_msb_pda_stack(2, 3, pda_tbl, 0, 56), (0, 1, 1))
        self.assertEqual(run_msb_pda_stack(2, 3, pda_tbl, 0, 224), (1, 0, 0))
        self.assertEqual(run_msb_pda_stack(2, 3, pda_tbl, 0, 12_416), (0, 1, 1))
        self.assertEqual(run_msb_pda_stack(2, 3, pda_tbl, 0, 49_664), (1, 0, 0))
        self.assertEqual(run_msb_pda_stack(2, 3, pda_tbl, 0, 8), (0, 1, 1))
        self.assertEqual(run_msb_pda_stack(2, 3, pda_tbl, 0, 32), (1, 0, 0))
        self.assertEqual(run_msb_pda_stack(2, 3, pda_tbl, 0, 512), (0, 1, 1))

        # Boundary & 6-tier cascade checks for T_diamond8 and Cone 9
        self.assertFalse(is_diamond8_cone9(33_462_157))
        self.assertFalse(is_diamond8_cone9(100_571_020))
        self.assertTrue(is_diamond8_cone9(100_571_021))  # 2^25 * 3 - 92275 (minimal Cone 9)
        self.assertFalse(is_diamond8_cone9((1 << 25) * 15 - 92_275))  # coprime23 == 5 != 1
        y_c8 = cousin_diamond8_step_int(100_571_021)
        self.assertEqual(y_c8, 37_714_133)
        self.assertTrue(is_diamond7_cone8(y_c8))
        self.assertGreater(cousin_diamond2_phi(y_c8), cousin_diamond2_phi(100_571_021))
        self.assertEqual(cousin_diamond8_step_int(37_714_133), 883_925)
        self.assertEqual(cousin_diamond8_step_int(883_925), 20_717)
        self.assertEqual(cousin_diamond8_step_int(20_717), 7_769)
        self.assertEqual(cousin_diamond8_block_return(1), (0, 1))
        self.assertEqual(cousin_diamond8_block_return(2), (1, 1))
        self.assertEqual(cousin_diamond8_block_return(3), (1, 5))
        self.assertEqual(cousin_diamond8_block_return(100_571_021), (16, 1))
        self.assertEqual(cousin_diamond8_step_int(-1), -1)
        self.assertEqual(cousin_diamond8_step_int(-5), -7)

        # Non-integer Q_(6)^+ rationals (including 100571021/7) ALWAYS bypass Cone 9
        cyc_1_7 = [Fraction(1, 7)]
        for _ in range(5):
            cyc_1_7.append(cousin_diamond8_step_q6(cyc_1_7[-1]))
        self.assertEqual(cyc_1_7[5], Fraction(1, 7))
        for den in (5, 7, 11, 13):
            for num in (1, 19, 12_548_309, 100_571_021, 100_571_021 * den - 92_275 * den + 1):
                f_q6 = Fraction(num, den)
                if f_q6.denominator > 1:
                    self.assertEqual(
                        cousin_diamond8_step_q6(f_q6),
                        cousin_diamond7_step_q6(f_q6),
                    )

        # Error-path validation across all Wave 11 primitives
        for bad_q in (0, -1, True, False, 1.5, "1"):
            with self.assertRaises(ValueError):
                run_lsb_one_counter_ocn(bad_q, [(0, 0)], [(0, 0)], 0, 5)  # type: ignore[arg-type]
        for bad_q0 in (-1, 1, True, False, "0"):
            with self.assertRaises(ValueError):
                run_lsb_one_counter_ocn(1, [(0, 0)], [(0, 0)], bad_q0, 5)  # type: ignore[arg-type]
        for bad_n_ocn in (0, -2, True, False, 2.5, "56"):
            with self.assertRaises(ValueError):
                run_lsb_one_counter_ocn(1, [(0, 0)], [(0, 0)], 0, bad_n_ocn)  # type: ignore[arg-type]
        for bad_c0 in (-1, True, False, 1.5, "0"):
            with self.assertRaises(ValueError):
                run_lsb_one_counter_ocn(1, [(0, 0)], [(0, 0)], 0, 5, c0=bad_c0)  # type: ignore[arg-type]
        for bad_dz in ([], [(0,)], [(-1, 0)], [(0, 2)], [(0, True)], [((1, 0), (0, 0))]):
            with self.assertRaises(ValueError):
                run_lsb_one_counter_ocn(1, bad_dz, [(0, 0)], 0, 5)  # type: ignore[arg-type]
        for bad_dp in ([], [(0,)], [(-2, 0)], [(0, 2)], [(0, True)], [((1, 0), (0, 0))]):
            with self.assertRaises(ValueError):
                run_lsb_one_counter_ocn(1, [(0, 0)], bad_dp, 0, 5)  # type: ignore[arg-type]
        with self.assertRaises(ValueError):
            run_lsb_one_counter_ocn(2, [(0, 0), (0, 0)], [(0, 0), (0, 0)], 0, 5)

        for det_fn in (
            laurent_twobase_6x6_t3u2_det_matrix,
            laurent_twobase_6x6_t3u2_det_closed,
            laurent_twobase_8x8_t4u2_det_matrix,
        ):
            for bad_args in ((-1, 2, 1), (2, -1, 1), (2, 3, 0), (True, 3, 1), (2, 3, False), (2.5, 3, 1)):
                with self.assertRaises(ValueError):
                    det_fn(*bad_args)  # type: ignore[arg-type]

        for bad_pda_args in (
            (0, 3, pda_tbl, 0, 8),
            (2, 0, pda_tbl, 0, 8),
            (True, 3, pda_tbl, 0, 8),
            (2, 3, pda_tbl, -1, 8),
            (2, 3, pda_tbl, 2, 8),
            (2, 3, pda_tbl, 0, 0),
            (2, 3, pda_tbl, 0, True),
            (2, 3, [], 0, 8),
            (2, 3, {}, 0, 8),
        ):
            with self.assertRaises(ValueError):
                run_msb_pda_stack(*bad_pda_args)  # type: ignore[arg-type]
        for bad_op in (("unknown",), ("pop", 1), ("replace", 3), ("push", 0, 3)):
            bad_tbl = dict(pda_tbl)
            bad_tbl[(0, 0, 1)] = (0, bad_op)
            with self.assertRaises(ValueError):
                run_msb_pda_stack(2, 3, bad_tbl, 0, 8)

        for bad_x in (True, False, 2.5, "100571021"):
            with self.assertRaises(ValueError):
                is_diamond8_cone9(bad_x)  # type: ignore[arg-type]
            with self.assertRaises(ValueError):
                cousin_diamond8_step_int(bad_x)  # type: ignore[arg-type]
            with self.assertRaises(ValueError):
                cousin_diamond8_step_q6(bad_x)  # type: ignore[arg-type]
        for bad_mul in (1, 2, 4, -3, True):
            with self.assertRaises(ValueError):
                cousin_diamond8_step_int(7, q=bad_mul)  # type: ignore[arg-type]
        for bad_pos in (0, -1, True):
            with self.assertRaises(ValueError):
                cousin_diamond8_block_return(bad_pos)  # type: ignore[arg-type]
        for bad_frac in (Fraction(1, 2), Fraction(1, 3), Fraction(5, 6)):
            with self.assertRaises(ValueError):
                cousin_diamond8_step_q6(bad_frac)

        # Constructive Mod-9 backward Collatz branch-descent happy/boundary/error checks
        for x_res9 in (5, 7, 8, 10, 11, 13):  # covers all 6 invertible mod-9 classes {5,7,8,1,2,4}
            nxt_b = mod9_backward_collatz_branch_next(lambda n_v: (1, n_v.bit_length()), x_res9)
            self.assertGreater(nxt_b, x_res9)
            self.assertGreaterEqual(nxt_b, 5)
            self.assertNotEqual(nxt_b % 3, 0)
            self.assertLessEqual(nxt_b, 128 * x_res9)
        for m0_cut in (3, 10, 25):
            cur_ev = 6 * m0_cut + 5
            for _ in range(5):
                nxt_ev = mod9_backward_collatz_branch_next(lambda n_v: (1, 1), cur_ev)
                self.assertGreater(nxt_ev, cur_ev)
                self.assertGreaterEqual(nxt_ev, 2 * m0_cut)
                self.assertNotEqual(nxt_ev % 3, 0)
                cur_ev = nxt_ev
        with self.assertRaises(ValueError):
            mod9_backward_collatz_branch_next("not_callable", 5)  # type: ignore[arg-type]
        for bad_bx in (0, 4, 6, 9, -5, True, False, 5.5, "5"):
            with self.assertRaises(ValueError):
                mod9_backward_collatz_branch_next(lambda n_v: (1, 1), bad_bx)  # type: ignore[arg-type]
        for bad_wt in ((0, 1), (1, 0), (-1, 2), (True, 1), (1,), "1/2"):
            with self.assertRaises(ValueError):
                mod9_backward_collatz_branch_next(lambda _n: bad_wt, 5)  # type: ignore[return-value]

        # Synthetic witness-bank check on all 5 Wave 11 dynamic predicates (proving zero hardcoded IDs)
        base_bank = load_witness_bank()
        with tempfile.TemporaryDirectory() as tmpdir:
            synth_bank = copy.deepcopy(base_bank)
            synth_bank["falsified_hypotheses"] = []
            synth_bank["domains"]["z_pos_high_glide"] = [
                {
                    "witness_id": "SYNTH_MIXED_Q2_OCN_794624_VS_3178496",
                    "seed": 529_749,
                    "next_compressed": 794_624,  # 97 * 2^13 (% 3 == 2): both MSB & LSB mixed Q=2 modes collide!
                    "ocn_q2_multi_even_preimage": 3_178_496,
                    "kills_mechanisms": ["mixed_q2_ocn"],
                },
                {
                    "witness_id": "SYNTH_D8_CONE9_K27_M1",
                    "seed": 3 * (1 << 27) - 92_275,  # 402560909: Cone 9 jumps Phi_2 upward into Cone 8!
                    "kills_mechanisms": ["phi2_on_diamond8"],
                },
                {
                    "witness_id": "SYNTH_DYADIC_LEN_M7_W3_SPLIT_141_VS_151",
                    "seed": 141,
                    "core_word": [1, 0, 0, 1, 0, 0, 0, 0, 1],
                    "dyadic_length_window_m": 7,
                    "dyadic_length_partner_word": [1, 1, 1],
                    "kills_mechanisms": ["length_blind_dyadic"],
                },
                {
                    "witness_id": "SYNTH_PDA_Q2_G3_20_VS_1280",
                    "seed": 13,
                    "next_compressed": 20,  # 20 % 3 == 2: PDA (Q=2, G=3) locks 20 vs 64 * 20 = 1280!
                    "pda_q2_g3_multi_even_preimage": 1_280,
                    "kills_mechanisms": ["pda_q2_g3"],
                },
                {
                    "witness_id": "SYNTH_ASYM_SLOPE_Q2_OCN_M8",
                    "seed": 5,
                    "next_compressed": 8,  # 8 % 3 == 2: w(16) + w(5) = 31/75 > 1/8 = w(8)!
                    "asym_ocn_even_preimage": 16,
                    "kills_mechanisms": ["asym_slope_q2_ocn"],
                },
            ]
            synth_bank["domains"]["log2_3_convergents"] = [
                {
                    "witness_id": "SYNTH_T3U2_EVEN_U2_ZERO_3_8_SYN",
                    "W": 3,
                    "K": 8,
                    "gap_sign": 1,
                    "laurent_twobase_6x6_t3u2_u": 2,
                    "kills_mechanisms": ["t3u2_even_u"],
                },
                {
                    "witness_id": "SYNTH_MOD24_5_17_ESCAPE_101_AND_233",
                    "W": 2,
                    "K": 4,
                    "gap_sign": 1,
                    "mod24_5_escape_prime": 101,
                    "mod24_17_escape_prime": 233,
                    "kills_mechanisms": ["mod24_5_17_escape"],
                },
                {
                    "witness_id": "SYNTH_T4U2_8X8_CONE_NEG_3_5",
                    "W": 3,
                    "K": 5,
                    "gap_sign": 1,
                    "laurent_twobase_8x8_t4u2_u1_det": -559_794_375,
                    "kills_mechanisms": ["t4u2_8x8_cone_pos"],
                },
            ]
            synth_p = Path(tmpdir) / "synth_w11.json"
            synth_p.write_text(json.dumps(synth_bank), encoding="utf-8")

            g1 = evaluate_hypothesis_against_witness_bank(
                "SynthMixedOCN", _dynamic_pred_mixed_sign_q2_ocn_mode_separates_preimages,
                domains=("z_pos_high_glide",), bank_path=synth_p,
            )
            self.assertEqual(g1["minimal_failure"], ("z_pos_high_glide", "SYNTH_MIXED_Q2_OCN_794624_VS_3178496"))
            g2 = evaluate_hypothesis_against_witness_bank(
                "SynthD8", _dynamic_pred_phi2_on_cousin_diamond8_outside_cones4to8,
                domains=("z_pos_high_glide",), bank_path=synth_p,
            )
            self.assertEqual(g2["minimal_failure"], ("z_pos_high_glide", "SYNTH_D8_CONE9_K27_M1"))
            g3 = evaluate_hypothesis_against_witness_bank(
                "SynthT3U2", _dynamic_pred_twobase_6x6_t3u2_even_u_nonzero_and_all_pos,
                domains=("log2_3_convergents",), bank_path=synth_p,
            )
            self.assertEqual(g3["minimal_failure"], ("log2_3_convergents", "SYNTH_T3U2_EVEN_U2_ZERO_3_8_SYN"))
            g4 = evaluate_hypothesis_against_witness_bank(
                "SynthMod24Escape", _dynamic_pred_mod24_5_17_prime_forces_even_gcd,
                domains=("log2_3_convergents",), bank_path=synth_p,
            )
            self.assertEqual(g4["minimal_failure"], ("log2_3_convergents", "SYNTH_MOD24_5_17_ESCAPE_101_AND_233"))
            g5 = evaluate_hypothesis_against_witness_bank(
                "SynthDyadicLenPin", _dynamic_pred_length_blind_dyadic_shift_pinning_or_subcritical,
                domains=("z_pos_high_glide",), bank_path=synth_p,
            )
            self.assertEqual(g5["minimal_failure"], ("z_pos_high_glide", "SYNTH_DYADIC_LEN_M7_W3_SPLIT_141_VS_151"))
            g6 = evaluate_hypothesis_against_witness_bank(
                "SynthPDAQ2G3", _dynamic_pred_pda_q2_g3_stack_separates_preimages,
                domains=("z_pos_high_glide",), bank_path=synth_p,
            )
            self.assertEqual(g6["minimal_failure"], ("z_pos_high_glide", "SYNTH_PDA_Q2_G3_20_VS_1280"))
            g7 = evaluate_hypothesis_against_witness_bank(
                "SynthT4U2Cone", _dynamic_pred_twobase_8x8_t4u2_cone_positivity,
                domains=("log2_3_convergents",), bank_path=synth_p,
            )
            self.assertEqual(g7["minimal_failure"], ("log2_3_convergents", "SYNTH_T4U2_8X8_CONE_NEG_3_5"))
            g8 = evaluate_hypothesis_against_witness_bank(
                "SynthAsymSlopeOCN", _dynamic_pred_asym_slope_q2_ocn_mersenne_bypass_weight,
                domains=("z_pos_high_glide",), bank_path=synth_p,
            )
            self.assertEqual(g8["minimal_failure"], ("z_pos_high_glide", "SYNTH_ASYM_SLOPE_Q2_OCN_M8"))

            # Verify primary ground-truth corruption detection across all 10 new Wave 11 witnesses
            corruptions = [
                ("z_pos_high_glide", "ZPOS_MIXED_SIGN_Q2_OCN_PREIMAGE_COLLAPSE", "ocn_q2_56_counter", 1),
                ("z_pos_high_glide", "ZPOS_COUSIN_DIAMOND8_CONE9_100571021_JUMP", "cousin_diamond8_steps_to_1", 15),
                ("z_pos_high_glide", "ZPOS_DYADIC_WINDOW_M6_W3_LENGTH_SPLIT_69_VS_75", "dyadic_length_partner_seed", 77),
                ("z_pos_high_glide", "ZPOS_PDA_STACK_Q2_G3_COLLISION_8_VS_512", "pda_q2_g3_multi_even_preimage", 256),
                ("z_pos_high_glide", "ZPOS_ASYMMETRIC_SLOPE_Q2_OCN_MERSENNE_BYPASS", "asym_ocn_target_sum", "5/16"),
                ("m1_q2_pos", "M1_COUSIN_DIAMOND8_1_OVER_7", "orbit", ["1/7", "5/7", "11/7", "20/7", "3/7"]),
                ("m3_supercritical", "M3_COUSIN_DIAMOND8_7X1_CYCLE5", "orbit", [5, 18, 9, 32, 11]),
                ("log2_3_convergents", "LAURENT_TWOBASE_6X6_T3U2_EVEN_U2_ZERO_3_8_AND_OUTER_FLIP", "laurent_twobase_6x6_t3u2_det", 1),
                ("log2_3_convergents", "RECIPROCITY_MOD24_5_17_ODD_GCD_ESCAPE_29_AND_89", "mod24_5_escape_ord32", 14),
                ("log2_3_convergents", "LAURENT_TWOBASE_8X8_T4U2_CONE_FLIP_3_5_VS_5_8", "laurent_twobase_8x8_t4u2_u1_det", 1),
            ]
            bad_b = copy.deepcopy(base_bank)
            for dom, wid, field, bad_val in corruptions:
                for item in bad_b["domains"][dom]:
                    if item["witness_id"] == wid:
                        item[field] = bad_val
            bad_p = Path(tmpdir) / "corrupt_w11_all10.json"
            bad_p.write_text(json.dumps(bad_b), encoding="utf-8")
            chk = verify_witness_bank_ground_truth(bad_p)
            self.assertFalse(chk["all_witnesses_ground_truth_verified"])
            for _, wid, _, _ in corruptions:
                self.assertIn(wid, chk["failed_witness_ids"], f"Missed corruption on {wid}")

            # Verify subtle secondary-field corruptions on Wave 11 witnesses
            subtle_corruptions = [
                ("z_pos_high_glide", "ZPOS_MIXED_SIGN_Q2_OCN_PREIMAGE_COLLAPSE", "ocn_q2_multi_even_preimage", 24_832),
                ("z_pos_high_glide", "ZPOS_COUSIN_DIAMOND8_CONE9_100571021_JUMP", "cousin_diamond8_next", 37_714_131),
                ("z_pos_high_glide", "ZPOS_DYADIC_WINDOW_M6_W3_LENGTH_SPLIT_69_VS_75", "dyadic_supercritical_excess", 10),
                ("z_pos_high_glide", "ZPOS_PDA_STACK_Q2_G3_COLLISION_8_VS_512", "pda_q2_g3_12416_height", 0),
                ("z_pos_high_glide", "ZPOS_ASYMMETRIC_SLOPE_Q2_OCN_MERSENNE_BYPASS", "asym_ocn_mersenne_k4_sum", "200/1225"),
                ("log2_3_convergents", "LAURENT_TWOBASE_6X6_T3U2_EVEN_U2_ZERO_3_8_AND_OUTER_FLIP", "t3u2_outer_neg_pair", [5, 8]),
                ("log2_3_convergents", "RECIPROCITY_MOD24_5_17_ODD_GCD_ESCAPE_29_AND_89", "cubic_excluded_ord2", 18),
                ("log2_3_convergents", "LAURENT_TWOBASE_8X8_T4U2_CONE_FLIP_3_5_VS_5_8", "t4u2_cone_pos_u4_pair", [3, 5]),
            ]
            bad_b2 = copy.deepcopy(base_bank)
            for dom, wid, field, bad_val in subtle_corruptions:
                for item in bad_b2["domains"][dom]:
                    if item["witness_id"] == wid:
                        item[field] = bad_val
            bad_p2 = Path(tmpdir) / "corrupt_w11_subtle.json"
            bad_p2.write_text(json.dumps(bad_b2), encoding="utf-8")
            chk2 = verify_witness_bank_ground_truth(bad_p2)
            self.assertFalse(chk2["all_witnesses_ground_truth_verified"])
            for _, wid, _, _ in subtle_corruptions:
                self.assertIn(wid, chk2["failed_witness_ids"], f"Missed subtle corruption on {wid}")

    def test_wave11_lean4_zero_custom_axioms_docstring_and_pii_audit(self) -> None:
        import re
        from collatz_analysis.formal_proofs import (
            ALLOWED_LEAN4_FOUNDATIONAL_AXIOMS,
            verify_lean4_kernel_proofs,
        )

        pkg_dir = Path(__file__).resolve().parent.parent
        res = verify_lean4_kernel_proofs()
        self.assertTrue(res["pure_kernel_verified"])
        self.assertTrue(res["zero_sorry_verified"])
        self.assertTrue(res["zero_warnings_verified"])
        self.assertEqual(len(res["lean_files"]), 61)
        self.assertEqual(res["theorems_audited"], 2253)
        self.assertEqual(res["axiom_free_theorem_count"], 611)
        self.assertTrue(any(Path(p).name == "Wave11WholeSpaceCore.lean" for p in res["lean_files"]))
        self.assertTrue(any(Path(p).name == "Wave11WholeSpace.lean" for p in res["lean_files"]))

        ax_map = res["axioms_by_theorem"]
        w11_theorems = (
            "artsGieslSemanticDP1D_interior_invariant_and_dp1_strict",
            "left_anchored_dp2_chain_reduction",
            "positive_parikh_syzygy_fast_blocks_all_omega_towers",
            "twosided_mod3_and_mod6_omit_r3_and_all11_certs",
            "r8CycleParikh_telescopes",
            "universal_left_model_mersenne_b1_t2_lock",
            "deltaL_flip2_period2_no_fixed_point_cert",
            "higher_left_carriers_k4_k8_and_mersenne_r8_lock",
            "sylow_prime_dvd_order_of_pow_ne_one",
            "full_two_sylow_dvd_order_of_half_minus_one",
            "complete_mod24_and_sylow_reciprocity_obstructions",
            "m_block_shared_mersenne_sylow_and_one_block_companion_cascades",
            "intDet_natAbs_le_fact_mul_colProd",
            "partialStretchMat_step_det",
            "laurent_single_base_all_T_exact_det",
            "laurent_universal_single_base_upgraded_confluent_and_laplace_bound",
            "twoBaseT3U2_poly_identity",
            "t3u2_odd_u_bracket_nonzero",
            "laurent_6x6_t3u2_factorization_and_cone_positivity",
            "laurent_8x8_twobase_t4u2_congruence_divisibility_and_cone_flip",
            "iterOCN1_eq_iterOCN0_flip",
            "asymSlopeQ2_mersenne_bypass_and_zpos_refutation_cert",
            "runMSBOneCounterOCN_counter_le_bitLength",
            "runLSBOneCounterOCN_counter_le_bitLength",
            "mod9ShiftTo8_spec",
            "poly_bitlength_denominator_preimage_impossibility",
            "unconditional_all_ocn_raw_counter_and_poly_bitlength_preimage_impossibility",
            "general_mixed_sign_ocn_preimage_impossibility",
            "canonical_pda_q2_g3_separates_and_collides_cert",
            "lsb_mixed_sign_ocn_raw_counter_impossibility_and_bounded_pda_pumping",
            "eventual_poly_bitlength_denominator_preimage_impossibility",
            "unconditional_general_pda_stack_height_and_arbitrary_init_ocn_impossibility",
            "cousinDiamond8StepInt_ofNat_eq",
            "cousin_diamond8_outside_cones4to9_strict_descent",
            "not_cone9_six_mul_pow9_sub1",
            "cousin_diamond8_cones4to9_exact_return",
            "cousin_diamond8_global_convergence",
            "cousin_diamond8_r_block_spiral_climb_and_laurent_impossibility",
            "cousin_diamond8_q6_noninteger_avoids_cone9",
            "cousin_diamond8_counter_model_separation",
            "first_hit_q0_iff_shift_ge_three_and_pow3_ones",
            "markovShift_mod162_bijection_and_five_ones_81_lock",
            "dyadic_window_supercritical_shift_multiplicity",
            "dyadic_window_surviving_leaves_mod162_fiber_and_cell_occupancy",
        )
        for thm in w11_theorems:
            self.assertIn(thm, ax_map)
            self.assertTrue(
                set(ax_map[thm]).issubset(ALLOWED_LEAN4_FOUNDATIONAL_AXIOMS),
                f"Unexpected custom axiom in {thm}: {ax_map[thm]}",
            )

        for axfree_thm in (
            "interior9_head_ne_L_and_nonempty",
            "srsReaches_omitR2_trans",
            "artsGieslSemanticDP1D_interior_invariant_and_dp1_strict",
            "getPairAtW11_replicate",
            "deltaL_flip2_period2_no_fixed_point_cert",
            "iterOCN1_eq_iterOCN0_flip",
            "asymSlopeQ2_mersenne_bypass_and_zpos_refutation_cert",
            "canonical_pda_q2_g3_separates_and_collides_cert",
            "not_cone9_of_mod3_ne_2",
            "cousin_diamond8_counter_model_separation",
        ):
            self.assertEqual(ax_map[axfree_thm], [], f"Expected [] axioms on {axfree_thm}")

        for choice_free_thm in (
            "universal_left_model_mersenne_b1_t2_lock",
            "higher_left_carriers_k4_k8_and_mersenne_r8_lock",
            "sylow_prime_dvd_order_of_pow_ne_one",
            "full_two_sylow_dvd_order_of_half_minus_one",
            "intDet_natAbs_le_fact_mul_colProd",
            "twoBaseT3U2_poly_identity",
            "poly_bitlength_denominator_preimage_impossibility",
            "unconditional_all_ocn_raw_counter_and_poly_bitlength_preimage_impossibility",
            "general_mixed_sign_ocn_preimage_impossibility",
            "lsb_mixed_sign_ocn_raw_counter_impossibility_and_bounded_pda_pumping",
            "eventual_poly_bitlength_denominator_preimage_impossibility",
            "unconditional_general_pda_stack_height_and_arbitrary_init_ocn_impossibility",
            "not_cone9_six_mul_pow9_sub1",
            "cousin_diamond8_q6_noninteger_avoids_cone9",
        ):
            self.assertNotIn(
                "Classical.choice",
                ax_map[choice_free_thm],
                f"Expected choice-free proof on {choice_free_thm}",
            )

        # Verify zero shell-escape control-byte corruption & zero duplicate imports in Wave 11 Lean modules
        for w11_mod in ("Wave11WholeSpaceCore.lean", "Wave11WholeSpace.lean"):
            mod_path = pkg_dir / "CollatzFormal" / w11_mod
            raw_bytes = mod_path.read_bytes()
            bad_ctrl = [b for b in set(raw_bytes) if b < 32 and b not in (10, 13)]
            self.assertEqual(bad_ctrl, [], f"Control-byte corruption in {w11_mod}: {bad_ctrl}")
            import_lines = [
                ln.strip()
                for ln in mod_path.read_text(encoding="utf-8").splitlines()
                if ln.strip().startswith("import ")
            ]
            self.assertEqual(
                len(import_lines),
                len(set(import_lines)),
                f"Duplicate import lines in {w11_mod}: {import_lines}",
            )

        w11_src = (
            (pkg_dir / "CollatzFormal/Wave11WholeSpaceCore.lean").read_text(encoding="utf-8")
            + "\n"
            + (pkg_dir / "CollatzFormal/Wave11WholeSpace.lean").read_text(encoding="utf-8")
        )
        self.assertNotIn("-> True :=", w11_src)
        self.assertNotIn("fun _ _ _ => trivial", w11_src)
        single_doc_pat = re.compile(
            r"(?:set_option[^\n]+\n\s*)*/--((?:(?!-/).)*?)-/\s*(?:set_option[^\n]+\n\s*)*(private\s+)?theorem\s+([A-Za-z0-9_']+)\b",
            flags=re.S,
        )
        doc_matches = single_doc_pat.findall(w11_src)
        self.assertEqual(len(doc_matches), 34)
        for doc, priv_kw, thm_name in doc_matches:
            if priv_kw.strip():
                self.assertNotIn("Theorem ", doc, f"Public Theorem docstring attached to private {thm_name}")
            else:
                self.assertIn(thm_name, ax_map, f"Unaudited theorem docstring on {thm_name}")
                m_hdr = re.search(r"Theorem\s+[A-Za-z0-9.']+\s*\(`([A-Za-z0-9_']+)`", doc)
                if m_hdr is not None:
                    self.assertEqual(m_hdr.group(1), thm_name, f"Mismatched docstring header on {thm_name}")
                if "`[]` axioms" in doc:
                    self.assertEqual(ax_map[thm_name], [], f"False []-axiom docstring on {thm_name}")
                if "choice-free" in doc:
                    self.assertNotIn("Classical.choice", ax_map[thm_name], f"False choice-free docstring on {thm_name}")

        axfree_claim_pats = (
            re.compile(r"`([A-Za-z0-9_']+)`\s*\(`\[\]`\s*axioms", flags=re.I),
            re.compile(r"`([A-Za-z0-9_']+)`\s*\[\s*`\[\]`\s*axioms\s*\]", flags=re.I),
            re.compile(r"`([A-Za-z0-9_']+)`\s*,\s*`\[\]`\s*axioms", flags=re.I),
        )
        choice_free_claim_pats = (
            re.compile(r"`([A-Za-z0-9_']+)`\s*\(\s*choice-free\b", flags=re.I),
            re.compile(r"`([A-Za-z0-9_']+)`\s*\[\s*choice-free\b", flags=re.I),
            re.compile(r"`([A-Za-z0-9_']+)`\s*,\s*choice-free\b", flags=re.I),
        )
        for doc_rel in (
            "CollatzFormal/Wave11WholeSpaceCore.lean",
            "CollatzFormal/Wave11WholeSpace.lean",
            "PROOF_SPACE_LEDGER.md",
            "MATHEMATICAL_FINDINGS.md",
            "README.md",
            "witness_bank.json",
        ):
            doc_txt = (pkg_dir / doc_rel).read_text(encoding="utf-8")
            for pat in axfree_claim_pats:
                for thm_ref in pat.findall(doc_txt):
                    self.assertEqual(
                        ax_map.get(thm_ref),
                        [],
                        f"False []-axiom claim in {doc_rel} on {thm_ref}: {ax_map.get(thm_ref)}",
                    )
            for pat in choice_free_claim_pats:
                for thm_ref in pat.findall(doc_txt):
                    self.assertIn(thm_ref, ax_map, f"Unknown choice-free theorem ref {thm_ref} in {doc_rel}")
                    self.assertNotIn(
                        "Classical.choice",
                        ax_map[thm_ref],
                        f"False choice-free claim in {doc_rel} on {thm_ref}: {ax_map[thm_ref]}",
                    )
        self.assertNotIn("(`[]` Axioms)", w11_src)

        # Repo-wide zero-PII / machine-path hygiene scan across tracked source & docs
        forbidden_tokens = (
            "Us" + "ers" + "\\",
            "Us" + "ers/",
            "/" + "home" + "/",
            "C:" + "\\",
            "C:" + "/",
        )
        for path in sorted(pkg_dir.rglob("*")):
            if ".lake" in path.parts or "__pycache__" in path.parts or path.is_dir():
                continue
            if path.suffix in {".py", ".lean", ".md", ".json", ".c"}:
                txt = path.read_text(encoding="utf-8")
                for tok in forbidden_tokens:
                    self.assertNotIn(tok, txt, f"Forbidden path token {tok!r} in {path.name}")

    def test_cli_summary_includes_wave11_loop_and_exit_gate(self) -> None:
        import contextlib
        import io
        from unittest import mock
        from collatz_analysis.cli import main as cli_main

        buf_sum = io.StringIO()
        with contextlib.redirect_stdout(buf_sum):
            rc_sum = cli_main(["--summary", "--dp-depth", "50"])
        self.assertEqual(rc_sum, 0)
        out = buf_sum.getvalue()
        self.assertIn("[Wave 11 Whole-Space Proof Loop]", out)
        self.assertIn("A=True, B=True", out)
        self.assertIn("C=True, T_diamond8=True, D=True", out)
        self.assertLess(
            out.index("[Wave 10 Whole-Space Proof Loop]"),
            out.index("[Wave 11 Whole-Space Proof Loop]"),
        )
        self.assertLess(
            out.index("[Wave 11 Whole-Space Proof Loop]"),
            out.index("[Lean 4 Kernel Verification]"),
        )

        failed_w11 = {
            "passed": False,
            "verdict": "FALSIFIED",
            "universality_gate_passed": True,
            "witness_bank_total_entries": 85,
            "witness_bank_falsified_count": 36,
            "witness_bank_ground_truth_verified": True,
            "front_a_dp_twosided_and_mersenne_r8": {
                "left_anchored_dp_and_omit_r2_termination_verified": True,
                "twosided_m3_m6_omit_r3_and_all11_cascades_verified": False,
                "universal_mersenne_b1_t2_lock_and_r8_cycle_verified": True,
                "higher_carriers_k2_4_8_m6_12_18_and_flip2_verified": True,
            },
            "front_b_reciprocity_sylow_and_laurent_t3u2": {
                "reciprocity_mod24_complete_and_sylow_verified": True,
                "twoblock_cubic_quintic_octic_floors_verified": False,
                "companion_quotient_cascades_and_mblock_sylow_verified": True,
                "confluent_t2_t3_extrapolation_8x8_and_laplace_verified": True,
                "laurent_8x8_twobase_t4u2_divisibility_and_cone_flip_verified": True,
                "laurent_6x6_t3u2_closed_form_odd_u_and_cone_pos_verified": True,
            },
            "front_c_general_mixed_sign_ocn_and_diamond8": {
                "general_mixed_sign_ocn_mode_and_dual_pumping_verified": False,
                "lsb_raw_counter_ocn_and_pda_two_counter_verified": True,
                "all_ocn_raw_counter_and_mod9_branch_descent_verified": True,
                "cousin_diamond8_outside_cones4to9_descent_verified": True,
                "cousin_diamond8_cone9_6tier_cascade_verified": False,
                "cousin_diamond8_countermodels_verified": True,
            },
            "front_d_supercritical_dyadic_and_markov_mod162": {
                "first_hit_shift_ge3_and_pow3_ones_verified": True,
                "markov_mod162_bijection_and_81_lock_verified": False,
                "dyadic_supercritical_shift_multiplicity_verified": True,
                "surviving_window_leaves_mod162_and_fiber_equidist_verified": True,
            },
        }
        buf_fail = io.StringIO()
        with mock.patch(
            "collatz_analysis.cs_cegar_redteam.run_wave11_whole_space_campaign",
            return_value=failed_w11,
        ), mock.patch(
            "collatz_analysis.cli.verify_lean4_kernel_proofs",
            return_value={"lean_available": False, "static_hygiene_clean": True},
        ), contextlib.redirect_stdout(buf_fail):
            rc_fail = cli_main(["--summary", "--dp-depth", "10"])
        self.assertEqual(rc_fail, 1)
        self.assertIn("A=False, B=False", buf_fail.getvalue())
        self.assertIn("T_diamond8=False, D=False", buf_fail.getvalue())


if __name__ == "__main__":
    unittest.main()
