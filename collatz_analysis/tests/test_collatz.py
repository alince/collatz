"""
Comprehensive unit test suite for the `collatz_analysis` package.
"""

from __future__ import annotations

import math
import re
import unittest
from fractions import Fraction

from collatz_analysis import (
    affine_parameters,
    analyze_cantor_cone_and_sturmian_2adic,
    analyze_tao_syracuse_mixing,
    beatty_sturmian_max_indices,
    brox_shifted_block_carry,
    bugeaud_laurent_padic_valuation_bound,
    carry_via_odd_indices,
    classify_5adic_unit_cycle_denominators,
    classify_all_z_2cycles_and_3cycles,
    classify_s_integer_1cycles_z_inv_30,
    classify_s_integer_2cycles_z_inv_30,
    collatz_compressed_step,
    compute_brox_effective_finiteness_bounds,
    compute_contractive_coalescence_sieve,
    compute_exact_stopping_time_dp,
    compute_min_cycle_length_bound,
    compute_progression_signature,
    cramer_large_deviation_parameters,
    exhaustive_cycle_search_up_to_k,
    extremal_carry_bounds,
    generate_full_proof_suite_report,
    generate_m92_reflective_hensel_bands,
    is_coefficient_surviving_prefix,
    is_surviving_mod1296_class,
    is_syracuse_forest_root,
    log2_3_continued_fraction,
    m_cycle_block_carry,
    parity_vector,
    prove_2cycle_nonexistence_up_to_weight,
    prove_m92_nonexistence_hensel_certificate,
    prove_m95_all_weight_nonexistence,
    prove_m96_m98_hensel_frontier,
    prove_m99_unconditional_hensel_frontier,
    prove_multistep_hensel_mcycle_nonexistence,
    prove_steiners_1cycle_theorem,
    prove_surviving_diamond_threshold_k34,
    prove_unconditional_mcycle_nonexistence,
    rational_cycle_for_parity_vector,
    run_two_vertex_hensel_bands,
    self_certify_garner_bootstrap,
    sharp_surviving_carry_max,
    syracuse_forest_val,
    ultrametric_decode_carry,
    verify_base2_transducer_state_growth,
    verify_beatty_sturmian_characterization,
    verify_boost_three_line_counter_model_matrix,
    verify_cantor_cone_rigidity_and_uncertainty,
    verify_catalan_mihailescu_unit_cycles,
    verify_counter_model_no_go_meta_theorem,
    verify_cyclic_shift_carry_collapse_and_reflective_hensel,
    verify_deficit_drift_complementarity_and_peak_bound,
    verify_garner_stopping_time_coincidence,
    verify_general_backward_merger_and_bit_exhaustion,
    verify_lean4_kernel_proofs,
    verify_lower_semiconvergent_pinch_and_baker_floor,
    verify_minimal_counterexample_rigidity_and_sturmian_obstruction,
    verify_minimal_divergent_coalescence_obstruction,
    verify_multi_root_syracuse_forest_and_fourier_mixing,
    verify_multiblock_rigidity_and_archimedean_coupling,
    verify_next_tier_boost_counter_model_matrix,
    verify_one_equation_diophantine_equivalence,
    verify_one_equation_parametric_families_and_density_obstruction,
    verify_one_sided_semiconvergent_records,
    verify_parity_bijection,
    verify_potential_collatz_merger_and_index45_horizon,
    verify_prime_denom_rigidity_and_two_vertex_frontier,
    verify_raney_cantor_cone_on_negative_cycles,
    verify_two_return_escape_and_mod1296_sieve,
    verify_unbounded_syracuse_predecessor_tree_growth,
    verify_zero_trust_gap_rational_log_and_m92_pipeline,
)
from collatz_analysis.goal_extensions import (
    _build_kd_threshold_table,
    _certify_single_hensel_subcase,
    _certify_windowed_exact_r_subcase,
    _run_hensel_root_chunk,
)


class TestParity2Adic(unittest.TestCase):
    def test_parity_bijection_and_hensel_inverse(self) -> None:
        for k in range(1, 11):
            res = verify_parity_bijection(k)
            self.assertTrue(res["is_bijection"])
            self.assertEqual(res["distinct_vectors"], 1 << k)

    def test_affine_decomposition_and_odd_step_identity(self) -> None:
        for n in range(1, 60):
            v = parity_vector(n, 12)
            k, w, carry = affine_parameters(v)
            self.assertEqual(k, 12)
            self.assertEqual(carry, carry_via_odd_indices(v))
            curr = n
            for _ in range(k):
                curr = collatz_compressed_step(curr)
            self.assertEqual(curr * (1 << k), (3**w) * n + carry)

    def test_extremal_carry_bounds(self) -> None:
        k = 8
        by_w: dict[int, list[int]] = {}
        for mask in range(1 << k):
            v = tuple((mask >> j) & 1 for j in range(k))
            _, w, carry = affine_parameters(v)
            by_w.setdefault(w, []).append(carry)

        for w, carries in by_w.items():
            c_min, c_max = extremal_carry_bounds(k, w)
            self.assertEqual(min(carries), c_min)
            self.assertEqual(max(carries), c_max)

    def test_bohm_sontacchi_rational_cycles(self) -> None:
        # Trivial positive cycle {1, 2} has v = (1, 0)
        cyc_pos = rational_cycle_for_parity_vector((1, 0))
        self.assertTrue(cyc_pos.is_positive_integer_cycle)
        self.assertEqual(cyc_pos.n0, Fraction(1, 1))
        self.assertEqual(cyc_pos.orbit, (Fraction(1, 1), Fraction(2, 1)))

        # Negative cycle {-5, -7, -10} has v = (1, 1, 0)
        cyc_neg5 = rational_cycle_for_parity_vector((1, 1, 0))
        self.assertFalse(cyc_neg5.is_positive_integer_cycle)
        self.assertEqual(cyc_neg5.n0, Fraction(-5, 1))
        self.assertEqual(cyc_neg5.orbit, (Fraction(-5, 1), Fraction(-7, 1), Fraction(-10, 1)))


class TestCyclesAndDiophantineBounds(unittest.TestCase):
    def test_continued_fraction_log2_3(self) -> None:
        convs = log2_3_continued_fraction(num_terms=15)
        partial_quotients = [c.partial_quotient for c in convs[:12]]
        # Known CF of log_2(3) = [1; 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, ...]
        self.assertEqual(partial_quotients, [1, 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2])
        # Check classic convergents (p, q): (1,1), (2,1), (3,2), (8,5), (19,12), (65,41), (84,53), (485,306), (1054,665), (24727,15601)
        expected_pq = [
            (1, 1),
            (2, 1),
            (3, 2),
            (8, 5),
            (19, 12),
            (65, 41),
            (84, 53),
            (485, 306),
            (1054, 665),
            (24727, 15601),
        ]
        self.assertEqual([(c.p, c.q) for c in convs[:10]], expected_pq)

    def test_steiner_1cycle_theorem(self) -> None:
        res = prove_steiners_1cycle_theorem()
        self.assertTrue(res["theorem_verified"])
        self.assertEqual(res["unique_positive_1cycle"], [(1, 2, 1)])
        self.assertEqual(res["baker_lmn_cutoff_w"], 11793)

    def test_eliahou_cycle_length_bounds(self) -> None:
        b68 = compute_min_cycle_length_bound(68.0)
        b71 = compute_min_cycle_length_bound(71.0)
        # Compressed steps k = 114,208,327,604; Uncompressed steps k + w = 186,265,759,595
        self.assertEqual(b68.min_compressed_length, 114_208_327_604)
        self.assertEqual(b68.min_uncompressed_length, 186_265_759_595)
        self.assertGreaterEqual(b71.min_uncompressed_length, b68.min_uncompressed_length)

    def test_exhaustive_z_cycles_and_catalan(self) -> None:
        cat = verify_catalan_mihailescu_unit_cycles(max_k=20)
        self.assertTrue(cat["exact_catalan_match"])

        cyc = exhaustive_cycle_search_up_to_k(max_k=11)
        # Unique positive cycle {1, 2} (2 cyclic shifts of (1, 0))
        self.assertEqual(len(cyc["primitive_positive_cycles"]), 2)
        # Negative cycles: {-1} (1 shift of (1,)), {-5, -7, -10} (3 shifts of (1,1,0)),
        # and the 11-cycle starting at -17 (11 shifts of length 11, w=7): total 1 + 3 + 11 = 15!
        self.assertEqual(len(cyc["primitive_negative_cycles"]), 15)


class TestStoppingTimeAndTaoMixing(unittest.TestCase):
    def test_beatty_sturmian_characterization(self) -> None:
        res = verify_beatty_sturmian_characterization(max_k=12)
        self.assertTrue(res["characterization_exact"])
        # Check Sturmian indices for w = 6: floor((m-1)*log_2(3)) for m=1..6 -> (0, 1, 3, 4, 6, 7)
        self.assertEqual(beatty_sturmian_max_indices(6), (0, 1, 3, 4, 6, 7))
        carry_4, vec_4 = sharp_surviving_carry_max(4)
        self.assertEqual(vec_4, (1, 1, 0, 1, 1))
        self.assertEqual(carry_4, 85)

    def test_stopping_time_dp_matches_brute_force(self) -> None:
        dp = compute_exact_stopping_time_dp(max_k=12)
        for k in range(1, 11):
            brute_surv = sum(
                1
                for mask in range(1 << k)
                if is_coefficient_surviving_prefix(tuple((mask >> j) & 1 for j in range(k)))
            )
            self.assertEqual(dp[k - 1].surviving_classes, brute_surv)

    def test_cramer_rate_and_garner_coincidence(self) -> None:
        cramer = cramer_large_deviation_parameters()
        self.assertAlmostEqual(cramer["asymptotic_decay_base_rho"], 0.96590655, places=6)

        garner = verify_garner_stopping_time_coincidence(limit_n=2000)
        self.assertTrue(garner["coincidence_verified"])
        self.assertEqual(garner["exceptions_count"], 0)

    def test_tao_3adic_memory_annihilation(self) -> None:
        for m in (2, 3, 4):
            tao = analyze_tao_syracuse_mixing(max_odd_n=3001, mod_power_3=m)
            self.assertTrue(tao["exact_memory_erasure_at_step_m"])
            # For steps t < m, coupling TV distance is strictly positive; at t >= m, it is 0
            for t in range(m - 1):
                self.assertGreater(tao["coupling_tv_by_step"][t], 0.05)
            for t in range(m - 1, len(tao["coupling_tv_by_step"])):
                self.assertLess(tao["coupling_tv_by_step"][t], 1e-14)

    def test_base2_transducer_state_growth(self) -> None:
        res = verify_base2_transducer_state_growth(max_w=6)
        for item in res:
            self.assertTrue(item.exact_match)
            self.assertEqual(item.reachable_carry_states, 3**item.w)


class TestUltrametricDiamondAndCoalescence(unittest.TestCase):
    def test_ultrametric_decode_carry_injectivity(self) -> None:
        for k in range(1, 10):
            for mask in range(1, 1 << k):
                v = tuple((mask >> j) & 1 for j in range(k))
                odd_indices = tuple(j for j, bit in enumerate(v) if bit == 1)
                w = len(odd_indices)
                _, _, carry = affine_parameters(v)
                recovered = ultrametric_decode_carry(carry, w)
                self.assertEqual(recovered, odd_indices)

    def test_surviving_diamond_threshold_k34_w22(self) -> None:
        res = prove_surviving_diamond_threshold_k34()
        self.assertEqual(res["sharp_threshold_k_star"], 34)
        self.assertEqual(res["sharp_threshold_w_star"], 22)
        self.assertEqual(res["minimal_k34_w22_pairs_count"], 5)
        self.assertTrue(res["all_gaps_equal_4"])
        for pair in res["minimal_k34_w22_pairs"]:
            self.assertEqual(pair.residue_low - pair.residue_high, 4)
            self.assertEqual(pair.carry_high - pair.carry_low, 4 * (3**22))
            # Verify progression identity T^34(2^34 * t + r_low) == T^34(2^34 * t + r_high) for t = 0, 1
            for t in (0, 1):
                nl = (t << 34) + pair.residue_low
                nh = (t << 34) + pair.residue_high
                for _ in range(34):
                    nl = collatz_compressed_step(nl)
                    nh = collatz_compressed_step(nh)
                self.assertEqual(nl, nh)
                self.assertEqual(nl, (3**22) * t + pair.common_image_b)

    def test_contractive_coalescence_sieve_and_k6_onset(self) -> None:
        sieve = compute_contractive_coalescence_sieve(max_k=14)
        stats = sieve["level_stats"]
        # No contractive coalescence for 1 <= k <= 5
        for k in range(1, 6):
            self.assertEqual(stats[k - 1]["newly_coalesced_at_k"], 0)
        # Sharp onset at k = 6 with exactly 1 branch: v = (1, 1, 1, 1, 0, 0) -> n = 64t + 15
        self.assertEqual(stats[5]["newly_coalesced_at_k"], 1)
        self.assertEqual(stats[5]["coeff_surviving_S_k"], 8)
        self.assertEqual(stats[5]["coalescence_pruned_active"], 7)

        sig = compute_progression_signature((1, 1, 1, 1, 0, 0))
        self.assertEqual(sig.r_v, 15)
        self.assertEqual(sig.b_v, 20)

    def test_mcycle_block_telescoping_and_2cycles(self) -> None:
        # Check Master Block-Telescoping Carry Identity against affine_parameters
        w_blocks = (3, 2, 4)
        a_blocks = (2, 1, 3)
        v: list[int] = []
        for wr, ar in zip(w_blocks, a_blocks):
            v.extend([1] * wr + [0] * ar)
        k1, w1, c1 = affine_parameters(v)
        k2, w2, c2 = m_cycle_block_carry(w_blocks, a_blocks)
        self.assertEqual((k1, w1, c1), (k2, w2, c2))

        res_2c = prove_2cycle_nonexistence_up_to_weight(max_W=50)
        self.assertTrue(res_2c["no_primitive_positive_2cycles"])
        self.assertEqual(res_2c["trivial_repetitions_found"], [(1, 1, 1, 1, 1)])


class TestFrontierReductionsAndNoGoTheorems(unittest.TestCase):
    def test_one_equation_diophantine_equivalence(self) -> None:
        res = verify_one_equation_diophantine_equivalence(max_n=250)
        self.assertTrue(res["equivalence_verified"])
        self.assertGreater(res["converse_solutions_verified_up_to_k12"], 100)

    def test_raney_cantor_cone_on_negative_cycles(self) -> None:
        res = verify_raney_cantor_cone_on_negative_cycles()
        self.assertTrue(res["all_have_S_infty_members"])
        self.assertEqual(res["negative_cycles_analyzed"], 3)

    def test_self_certified_garner_bootstrap(self) -> None:
        res = self_certify_garner_bootstrap(limit_n=72058, sieve_k=14, max_w_scan=2000)
        # B(306) = 72,058; next record is at w0 = 971, k0 = 1539 (B = 238,670)
        self.assertEqual(res["self_certified_garner_and_cycle_free_up_to_k"], 1538)
        self.assertEqual(res["self_certified_garner_and_cycle_free_up_to_w"], 970)
        self.assertEqual(res["self_certified_uncompressed_cycle_bound"], 2508)

    def test_counter_model_no_go_meta_theorem(self) -> None:
        res = verify_counter_model_no_go_meta_theorem()
        self.assertTrue(res["meta_theorem_verified"])
        self.assertEqual(res["model_M1_positive_2adic_rational_cycle"]["n0"], "19/5")
        self.assertEqual(res["model_M2_negative_integer_nonunit_cycle"]["denominator_gap"], -139)
        self.assertEqual(res["model_M3_5n_plus_1_positive_integer_cycles"]["denominator_gap"], 3)

    def test_cantor_cone_and_sturmian_2adic_theorem_13(self) -> None:
        res = analyze_cantor_cone_and_sturmian_2adic(bits=64, max_w_norm=200)
        self.assertTrue(res["sturmian_excluded_from_Z_minus"])
        self.assertTrue(res["non_stabilized_both_bits_present"])
        self.assertGreater(res["min_observed_C_over_w_3w"], 1.0 / 6.0)
        self.assertLessEqual(res["max_observed_C_over_w_3w"], 1.0 / 3.0)
        self.assertEqual(
            [r["exact_abs_x"] for r in res["negative_cantor_cone_series_duality"]],
            [1, 5, 17],
        )

    def test_unconditional_mcycle_nonexistence_theorem_14(self) -> None:
        sc = verify_one_sided_semiconvergent_records(max_w=5000)
        self.assertTrue(sc["exact_sequence_match"])
        self.assertEqual(sc["record_count"], 18)

        res_72k = prove_unconditional_mcycle_nonexistence(N0=72058, max_m=18)
        self.assertEqual(res_72k["max_m_proved_unconditionally"], 14)

        res_206m = prove_unconditional_mcycle_nonexistence(N0=206178386, max_m=32)
        self.assertEqual(res_206m["max_m_proved_unconditionally"], 28)

        res_68 = prove_unconditional_mcycle_nonexistence(N0=1 << 68, max_m=92)
        self.assertEqual(res_68["max_m_proved_unconditionally"], 88)

        res_71 = prove_unconditional_mcycle_nonexistence(N0=1 << 71, max_m=95)
        self.assertEqual(res_71["max_m_proved_unconditionally"], 91)
        self.assertEqual(res_71["bottleneck_at_next_m"]["failed_at_m"], 92)
        self.assertEqual(res_71["bottleneck_at_next_m"]["convergent_index"], 43)

    def test_full_proof_suite_report(self) -> None:
        report = generate_full_proof_suite_report()
        self.assertEqual(
            report["theorem_14_unconditional_mcycle_nonexistence"]["barina_2_pow_71_max_m"],
            91,
        )
        self.assertEqual(
            report["theorem_15_m92_hensel_and_brox_finiteness"]["barina_2_pow_71_max_m_with_hensel"],
            92,
        )
        self.assertEqual(
            report["theorem_19_multistep_hensel_and_index45_horizon"]["max_m_proved_unconditionally"],
            94,
        )
        self.assertTrue(
            report["theorem_20_z_2_3_cycles_and_s_integer_2cycles"]["z_2cycles_and_3cycles"][
                "zero_primitive_z_3cycles_verified"
            ]
        )
        self.assertTrue(
            report["theorem_21_carry_deficit_and_lower_semiconvergent_pinch"][
                "deficit_drift_and_peak_bound"
            ]["quadratic_peak_bound_verified"]
        )
        self.assertEqual(
            report["theorem_22_5adic_unit_denominators_and_coalescence_obstruction"][
                "five_adic_unit_denominators"
            ]["solution_count"],
            8,
        )
        self.assertTrue(
            report["theorems_29_to_31_next_tier_boost_and_counter_model_matrix"][
                "all_next_tier_mechanisms_verified"
            ]
        )
        self.assertTrue(report["wave4_whole_space_campaign"]["passed"])
        self.assertTrue(report["wave5_whole_space_campaign"]["passed"])
        self.assertTrue(report["wave6_whole_space_campaign"]["passed"])
        self.assertTrue(report["wave7_whole_space_campaign"]["passed"])


class TestBoostObstructionsTheorems15To18(unittest.TestCase):
    def test_theorem_15a_m92_hensel_certificate_and_prime_scan(self) -> None:
        res = prove_m92_nonexistence_hensel_certificate(N0=1 << 71, prime_scan_limit=200_000)
        self.assertEqual(res["max_m_proved_unconditionally"], 92)
        cert = res["certificate_m92"]
        self.assertTrue(cert.proved_nonexistent)
        self.assertEqual(cert.surviving_candidates, 0)
        self.assertEqual(cert.unique_candidate_p, 325_919_355_854_421_968_365)
        self.assertEqual(cert.unique_candidate_q, 205_632_218_873_398_596_256)
        self.assertEqual(res["multiple_confinement_92_to_96"][92], [1])
        self.assertEqual(res["multiple_confinement_92_to_96"][95], [1, 2, 3, 4])
        # D_9 has 5^2 = 25; D_43 has zero prime factors <= 200,000
        self.assertEqual(res["bottleneck_prime_factor_scan"][9]["factors_up_to_limit"], [(5, 25)])
        self.assertEqual(res["bottleneck_prime_factor_scan"][43]["factors_up_to_limit"], [])
        self.assertTrue(res["hercher_collatz_merger_check"]["identity_exact"])

    def test_theorem_15b_brox_shifted_carry_and_effective_finiteness(self) -> None:
        # Verify exact compression identity on a 3-block tuple (w=(2, 3, 1), a=(1, 2, 4))
        wb = (2, 3, 1)
        ab = (1, 2, 4)
        k_tot, w_tot, hs = brox_shifted_block_carry(wb, ab)
        denom = (1 << k_tot) - (3**w_tot)
        for j in range(3):
            wb_rot = wb[j:] + wb[:j]
            ab_rot = ab[j:] + ab[:j]
            _, _, c_rot = m_cycle_block_carry(wb_rot, ab_rot)
            self.assertEqual(hs[j] << wb[j], c_rot + denom)
            self.assertEqual(hs[j] & 1, 1)

        brox_res = compute_brox_effective_finiteness_bounds(max_m=5)
        bounds = brox_res["bounds"]
        self.assertEqual(len(bounds), 5)
        # m = 1 LMN cutoff ~ 11,792; m = 2 ~ 30,486; strictly increasing in m
        self.assertGreaterEqual(bounds[0].w_max_lmn, 11790)
        self.assertLessEqual(bounds[0].w_max_lmn, 11800)
        for i in range(4):
            self.assertLess(bounds[i].w_max_lmn, bounds[i + 1].w_max_lmn)

    def test_theorem_16_padic_baker_and_z_inv_30_classification(self) -> None:
        # Check Bugeaud-Laurent valuation bound at p = 5 and p = 7
        v5_ub = bugeaud_laurent_padic_valuation_bound(k=5, w=3, p=5)
        self.assertGreaterEqual(v5_ub, 1)
        v7_ub = bugeaud_laurent_padic_valuation_bound(k=10, w=6, p=7)
        self.assertGreaterEqual(v7_ub, 1)

        s_res = classify_s_integer_1cycles_z_inv_30()
        self.assertEqual(s_res["baker_bugeaud_laurent_w_max"], 39657)
        self.assertEqual(
            s_res["negative_1cycles"],
            [Fraction(-5, 1), Fraction(-1, 1)],
        )
        self.assertEqual(
            s_res["positive_1cycles"],
            [Fraction(1, 125), Fraction(1, 5), Fraction(1, 1), Fraction(19, 5)],
        )

    def test_theorems_17_and_18_cantor_cone_rigidity_and_uncertainty(self) -> None:
        rig = verify_cantor_cone_rigidity_and_uncertainty(max_n_sample=200, sturm_depth=120)
        self.assertEqual(rig["commutator_curvature"], "-1/4")
        # r = 1 shift of v*(infty) exits at step k = 2; r = 2 exits at k = 1; r = 3 exits at k = 8
        self.assertEqual(rig["sturmian_forward_shift_exits_1_to_35"][1], 2)
        self.assertEqual(rig["sturmian_forward_shift_exits_1_to_35"][2], 1)
        self.assertEqual(rig["sturmian_forward_shift_exits_1_to_35"][3], 8)
        self.assertGreater(rig["positive_3adic_exact_integer_matches_n27"], 45)
        self.assertGreater(rig["surviving_prefixes_uncertainty_verified"], 500)
        self.assertGreater(rig["min_observed_uncertainty_ratio_over_nw_div_3"], 1.0)
        self.assertEqual(rig["independent_toggles_in_first_78_odd_steps"], 32)
        self.assertTrue(rig["continuum_subcone_S_infty_div_disjoint_from_Z_minus"])


class TestGoalExtensionsTheorems19To22(unittest.TestCase):
    def test_theorem_19a_potential_merger_and_index45_adversarial_boundaries(self) -> None:
        h = verify_potential_collatz_merger_and_index45_horizon(N0=1 << 71)
        self.assertTrue(h["merger_and_potential_verified"])
        self.assertGreater(h["potential_samples_checked"], 250)
        # Analytic upgrade at Barina 2^68: m <= 89 proved (upgrades Theorem 14's m <= 88)
        self.assertEqual(h["barina_2_pow_68_upgraded_max_m"], 89)
        # Lattice confinement to u * (p_43, q_43) holds up to m = 99 and breaks at m = 100
        self.assertEqual(h["barina_2_pow_71_q43_confinement_max_m"], 99)
        # Convergent index 45 (q_45 = 31,150,961,018,190,238,869,556) eliminated for 1 <= m <= 101, enters at m = 102
        self.assertEqual(h["convergent_45_q"], 31_150_961_018_190_238_869_556)
        self.assertEqual(h["convergent_45_eliminated_up_to_m"], 101)
        self.assertEqual(h["convergent_45_first_enters_at_m"], 102)
        self.assertGreater(h["min_log2_N0_to_clear_q45_analytically"], 73.9)

        recs_by_m = {r.m: r for r in h["horizon_records_71"]}
        self.assertEqual(len(recs_by_m[91].surviving_semiconvergents), 0)
        self.assertTrue(recs_by_m[99].confined_to_q43_multiples)
        self.assertFalse(recs_by_m[100].confined_to_q43_multiples)
        self.assertTrue(recs_by_m[101].index45_eliminated)
        self.assertFalse(recs_by_m[102].index45_eliminated)

        # Adversarial boundary check: non-contiguous clamped-only potential fails 2/(3*N0)
        # whereas contiguous arc potential satisfies < 2*L/(3*N0) + 1/(3*N0)
        n0_adv = 10_000
        x1 = 2 * n0_adv + 3  # >= 2*N0 + 3 (Entry Merger satisfied!)
        k1 = 9
        # Suppose x1 jumps to x2 ~ (3/2)^9 / 2^4 * x1 ~ 2.4 * x1 > N0
        x2 = int(((3**k1) * (x1 + 1)) // (1 << (k1 + 4))) - 1
        non_contig_term = Fraction((3**k1) - (2**k1), (3**k1) * x1)
        # Notice without the +1/3*(1/x2 - 1/x1) telescoping shift, a single step at 2*N0+3
        # contributes ~0.487/N0, and at ell_1 = 1 (where x1 = N0 + 1 is allowed!),
        # (1 - (2/3)^9) / (N0 + 1) = 0.9739 / N0 > 2 / (3 * N0) = 0.6667 / N0!
        x1_ell1 = n0_adv + 1
        x2_ell1 = ((3**k1) * (x1_ell1 + 1)) // (1 << (k1 + 1)) - 1
        raw_clamped = Fraction((3**k1) - (2**k1), (3**k1) * x1_ell1)
        self.assertGreater(raw_clamped, Fraction(2, 3 * n0_adv))
        shifted_step = raw_clamped + Fraction(1, 3) * (Fraction(1, x2_ell1) - Fraction(1, x1_ell1))
        self.assertLess(shifted_step, Fraction(2, 3 * n0_adv))

    def test_theorem_19b_multistep_hensel_m94_and_genuine_r2_survivors(self) -> None:
        res = prove_multistep_hensel_mcycle_nonexistence(
            N0=1 << 71, max_m_full=94, eliminate_higher_multiples_up_to_m=95
        )
        self.assertEqual(res["max_m_proved_unconditionally"], 94)
        self.assertEqual(res["total_cycle_survivors"], 0)
        self.assertEqual(res["monotone_tail_cutoff_u_by_m"], {92: 2, 93: 3, 94: 4, 95: 5})
        self.assertEqual(res["higher_multiples_eliminated_by_m"][94], [2, 3])
        self.assertEqual(res["higher_multiples_eliminated_by_m"][95], [2, 3, 4])

        certs = {(c.m, c.u_mult, c.s_regime): c for c in res["subcase_certificates"]}
        # Adversarial check: at m = 94, u = 1, tight per-k1 bands prune s = 1 to 0, while s >= 2
        # finds 5 genuine r <= 2 arithmetic Hensel survivors (proving multi-step I_1 traversals exist!)
        c94_s1 = certs[(94, 1, "s=1")]
        c94_s2 = certs[(94, 1, "s>=2")]
        self.assertEqual(len(c94_s1.arithmetic_survivors), 0)
        self.assertEqual(len(c94_s2.arithmetic_survivors), 5)
        self.assertEqual(c94_s2.cycle_survivors, 0)
        self.assertEqual(c94_s2.max_drop_blocks, 81)

        # Adversarial check: at m = 95, u = 2 (s>=2) finds 25 and u = 3 (s>=2) finds 2 (27 total)
        c95_u2_s2 = certs[(95, 2, "s>=2")]
        c95_u3_s2 = certs[(95, 3, "s>=2")]
        self.assertEqual(len(c95_u2_s2.arithmetic_survivors), 25)
        self.assertEqual(len(c95_u3_s2.arithmetic_survivors), 2)
        self.assertEqual(len(res["distinct_arithmetic_hensel_survivors"]), 32)

        # Independently trace every single arithmetic Hensel survivor via compressed Collatz steps
        # to verify it > 2^71 initially and drops strictly <= 2^71!
        n0 = 1 << 71
        for z in res["distinct_arithmetic_hensel_survivors"]:
            self.assertEqual(z & 1, 1)
            self.assertGreater(z, n0)
            cur = z
            dropped = False
            for _ in range(4000):
                cur = collatz_compressed_step(cur)
                if cur <= n0:
                    dropped = True
                    break
            self.assertTrue(dropped)

    def test_theorem_20_z_2_3_cycles_and_s_integer_2cycles_adversarial(self) -> None:
        z_res = classify_all_z_2cycles_and_3cycles()
        self.assertEqual(z_res["w_brox_2"], 30486)
        self.assertEqual(z_res["w_brox_3"], 60117)
        self.assertTrue(z_res["simons_2005_n0_free_verified"])
        self.assertTrue(z_res["zero_primitive_z_3cycles_verified"])
        self.assertEqual(len(z_res["primitive_z_2cycles"]), 1)
        prim2 = z_res["primitive_z_2cycles"][0]
        self.assertEqual(set(prim2.local_minima), {-17, -41})
        self.assertEqual(prim2.denominator_gap, -139)

        # Adversarial check on m = 3: zero primitive 3-cycles, while the 2 unreduced
        # 3-fold repetitions (+1 and -5) ARE found by the canonical classifier!
        self.assertEqual(len(z_res["primitive_z_3cycles"]), 0)
        unreduced_3_mins = {r.local_minima for r in z_res["all_z_3cycles"]}
        self.assertEqual(unreduced_3_mins, {(1, 1, 1), (-5, -5, -5)})

        s2_res = classify_s_integer_2cycles_z_inv_30()
        self.assertGreaterEqual(s2_res["certified_w_max"], 100_000)
        self.assertEqual(len(s2_res["primitive_2cycles"]), 2)
        prim_sets = {frozenset((c.x1, c.x2)) for c in s2_res["primitive_2cycles"]}
        self.assertEqual(
            prim_sets,
            {
                frozenset((Fraction(-17, 1), Fraction(-41, 1))),
                frozenset((Fraction(29, 5), Fraction(23, 5))),
            },
        )
        # Adversarial check: 5 unreduced 2-fold repetitions match {1, 1/5, 1/125, -5, 19/5}
        rep_vals = {c.x1 for c in s2_res["repeated_1cycles"]}
        self.assertEqual(
            rep_vals,
            {
                Fraction(1, 1),
                Fraction(1, 5),
                Fraction(1, 125),
                Fraction(-5, 1),
                Fraction(19, 5),
            },
        )

        # Explicitly simulate rational Collatz map on 29/5 over 5 compressed steps
        cur = Fraction(29, 5)
        orbit = [cur]
        for _ in range(5):
            if cur.numerator % 2 == 0:
                cur = cur / 2
            else:
                cur = (3 * cur + 1) / 2
            orbit.append(cur)
        self.assertEqual(
            orbit,
            [
                Fraction(29, 5),
                Fraction(46, 5),
                Fraction(23, 5),
                Fraction(37, 5),
                Fraction(58, 5),
                Fraction(29, 5),
            ],
        )

    def test_theorem_21_deficit_complementarity_quadratic_peak_and_pinches(self) -> None:
        d_res = verify_deficit_drift_complementarity_and_peak_bound(max_n=300)
        self.assertTrue(d_res["complementarity_verified"])
        self.assertTrue(d_res["quadratic_peak_bound_verified"])
        self.assertGreater(d_res["surviving_prefixes_checked"], 800)
        self.assertGreater(d_res["odd_step_equalities_verified"], 400)
        self.assertGreater(d_res["min_observed_peak_over_bound_ratio"], 1.0)

        # Adversarial boundary check on n = 27 at k = 1 and k = tau(27) - 1 = 58
        cur = 27
        w = 0
        peak = 27
        theta = math.log2(3.0)
        for k in range(1, 59):
            if cur & 1:
                w += 1
            cur = collatz_compressed_step(cur)
            peak = max(peak, cur)
            self.assertGreater(3**w, 1 << k)
            quad_lb = 0.5 * (27.0 + math.sqrt(27.0 * 27.0 + (4.0 / 3.0) * 27.0 * w))
            self.assertGreater(peak, quad_lb)
            tmp = cur
            j_next = k
            while (tmp & 1) == 0:
                tmp >>= 1
                j_next += 1
            delta_k = w * theta - k
            delta_next = w * theta - j_next
            self.assertAlmostEqual(delta_k - delta_next, float(j_next - k), places=11)
        # Step k = 59 exits the surviving cone (3^w <= 2^59)
        if cur & 1:
            w += 1
        self.assertLessEqual(3**w, 1 << 59)

        p_res = verify_lower_semiconvergent_pinch_and_baker_floor(max_w=5000, max_n_sample=120)
        self.assertTrue(p_res["exact_lower_semiconvergent_match"])
        self.assertTrue(p_res["individual_step_baker_floor_verified"])
        first_three_wk = [(r.w, r.k) for r in p_res["records"][:3]]
        self.assertEqual(first_three_wk, [(1, 1), (2, 3), (7, 11)])

    def test_theorem_22_5adic_unit_denominators_and_coalescence_sharpness(self) -> None:
        u_res = classify_5adic_unit_cycle_denominators()
        self.assertEqual(u_res["solution_count"], 8)
        self.assertEqual(u_res["min_k_forcing_prime_ge_7_on_S_infty"], 4)
        self.assertEqual(u_res["min_k_forcing_prime_ge_7_globally"], 8)
        expected = {
            (1, 1, 0, -1),
            (2, 1, 0, 1),
            (3, 2, 0, -1),
            (2, 2, 1, -5),
            (3, 1, 1, 5),
            (5, 3, 1, 5),
            (1, 3, 2, -25),
            (7, 1, 3, 125),
        }
        actual = {(s.k, s.w, s.e, s.signed_diff) for s in u_res["solutions"]}
        self.assertEqual(actual, expected)

        # Adversarial check: for every surviving (k, w) with 4 <= k <= 60 (w < k and 3^w > 2^k),
        # |2^k - 3^w| after stripping powers of 5 is strictly >= 7!
        for k in range(4, 61):
            w_min = math.ceil(k * math.log(2.0) / math.log(3.0))
            for w in range(w_min, k + 1):
                if (3**w) <= (1 << k):
                    continue
                d = (3**w) - (1 << k)
                while d % 5 == 0:
                    d //= 5
                self.assertGreaterEqual(d, 7)

        c_res = verify_minimal_divergent_coalescence_obstruction(max_k=17)
        self.assertTrue(c_res["all_t_min_zero_n0_free"])
        self.assertEqual(c_res["max_N_coal_up_to_k16"], 64703)
        self.assertTrue(c_res["self_certified_72058_covers_k16"])
        self.assertEqual(c_res["max_N_coal_up_to_max_k"], 130799)
        self.assertTrue(c_res["self_certified_206M_covers_max_k"])
        self.assertEqual(
            c_res["newly_coalesced_nodes_verified"],
            c_res["boundary_witnesses_verified"],
        )

        # Adversarial boundary sharpness check on the closed-form threshold t_min:
        # across both negative-q0 regimes (forcing t_pos >= 1) and large-q0 regimes
        # (forcing t_contr >= 1), t = t_min satisfies 1 <= n' < n_0 while t = t_min - 1
        # strictly violates 1 <= n' < n_0!
        k, kp, w, wp = 8, 2, 5, 2
        p3_d = 3 ** (w - wp)  # 27 < 2^(8 - 2) = 64
        denom = (1 << k) - (1 << kp) * p3_d  # 256 - 108 = 148 > 0
        r_v, r_vp = 19, 3
        for q0 in (-80, -27, -1, 0, 5, 45, 200):
            t_pos = (-q0 + p3_d - 1) // p3_d if q0 < 0 else 0
            num = (1 << kp) * q0 + r_vp - r_v
            t_contr = (num // denom) + 1 if num >= 0 else 0
            t_min = max(0, t_pos, t_contr)
            n0_min = (1 << k) * t_min + r_v
            np_min = (1 << kp) * (p3_d * t_min + q0) + r_vp
            self.assertTrue(1 <= np_min < n0_min)
            if t_min >= 1:
                t_prev = t_min - 1
                n0_prev = (1 << k) * t_prev + r_v
                np_prev = (1 << kp) * (p3_d * t_prev + q0) + r_vp
                self.assertFalse(1 <= np_prev < n0_prev)

    def test_lean4_kernel_verification_zero_sorry(self) -> None:
        res = verify_lean4_kernel_proofs()
        self.assertTrue(res["static_hygiene_clean"])
        self.assertTrue(res["lean_available"], "Expected elan/Lean 4 toolchain to be installed")
        self.assertEqual(res["returncode"], 0, f"Lean 4 diagnostics: {res.get('stderr')}")
        self.assertEqual(res["stderr"], "", f"Lean 4 stdout/stderr diagnostics: {res.get('stderr')}")
        self.assertTrue(
            res["zero_warnings_verified"],
            f"Lean 4 warnings: {res.get('stderr')}",
        )
        self.assertTrue(res["zero_sorry_verified"])
        self.assertTrue(res["pure_kernel_verified"])
        self.assertGreaterEqual(res["theorems_audited"], 67)
        self.assertGreaterEqual(res["axiom_free_theorem_count"], 18)
        # Ensure ground certificates for all 32 Hensel survivors and unimodular determinants
        # depend on ZERO axioms in the Lean 4 kernel:
        ax_map = res["axioms_by_theorem"]
        self.assertEqual(ax_map["all_32_hensel_survivors_drop_below_2_pow_71"], [])
        self.assertEqual(ax_map["convergents_43_and_45_unimodular"], [])
        self.assertIn("affine_decomposition_universal", ax_map)
        self.assertIn("bohm_sontacchi_cycle_equation_universal", ax_map)
        self.assertIn("one_equation_forward_universal", ax_map)
        self.assertIn("one_cycle_carry_closed_form_universal", ax_map)
        self.assertIn("potential_telescoping_case2_cleared_denom", ax_map)
        self.assertIn("minimal_divergent_coalescence_universal", ax_map)
        self.assertIn("spiral_hensel_identity_universal", ax_map)
        self.assertIn("quadratic_peak_floor_cleared_square", ax_map)
        self.assertIn("collatz_standard_iff_compressed", ax_map)
        self.assertIn("collatz_iff_strict_descent", ax_map)
        self.assertIn("collatz_iff_two_barriers", ax_map)
        self.assertIn("one_equation_converse_universal", ax_map)
        self.assertIn("collatz_iff_one_equation_diophantine", ax_map)
        # Verify Theorems 23-25 + Section 11D recursive multi-step Hensel verifier
        # (427 total theorems, 154 completely axiom-free []):
        self.assertGreaterEqual(res["theorems_audited"], 427)
        self.assertGreaterEqual(res["axiom_free_theorem_count"], 154)
        self.assertEqual(ax_map["m92_two_step_hensel_kernel_verified"], [])
        self.assertEqual(ax_map["m92_nonactive_bounds_kernel_verified"], [])
        self.assertEqual(ax_map["all_55_new_m95_hensel_survivors_drop_below_2_pow_71"], [])
        self.assertEqual(ax_map["rational_log2_3_convergent_bounds"], [])
        self.assertEqual(ax_map["sturmian_w2_mod9_disjoint"], [])
        self.assertEqual(ax_map["lookup6Step_certified"], [])
        self.assertEqual(ax_map["hensel_96_98_batch0_ok"], [])
        self.assertEqual(ax_map["hensel_96_98_batch100_ok"], [])
        self.assertEqual(ax_map["exactM92_hensel_bridge_certified"], [])
        self.assertEqual(ax_map["convergent_signs_and_relations_certified"], [])
        self.assertIn("end_expanding_coalescence_reduces_to_suffix", ax_map)
        self.assertIn("m92_all_k1_hensel_complete", ax_map)
        self.assertIn("checkHenselNode_sound", ax_map)
        self.assertIn("verifyMultiStepHenselBand_sound", ax_map)
        self.assertIn("m93_multistep_hensel_kernel_verified", ax_map)
        self.assertIn("odd_multiplier_merger_unique_q3", ax_map)
        self.assertIn("strict_descent_minimal_counterexample_coalescence_contradiction", ax_map)
        self.assertIn("hercher_entry_merger_a1_ge_2", ax_map)
        self.assertIn("cyclic_shift_carry_dvd_iff", ax_map)
        self.assertIn("verifyTwoStepHenselCert_sound", ax_map)
        self.assertIn("one_equation_forces_pos", ax_map)
        self.assertIn("carry_sub_pow2_not_dvd_pow3", ax_map)
        self.assertIn("one_equation_pow2_le_pow4_mul", ax_map)
        self.assertIn("one_equation_geometric_family", ax_map)
        self.assertIn("no_nontrivial_spiral_cycles_1_to_92", ax_map)
        self.assertIn("all_new_m96_to_98_hensel_survivors_drop_below_2_pow_71", ax_map)
        self.assertIn("m96_to_98_hensel_survivor_drop_universal", ax_map)
        self.assertIn("minimal_counterexample_archimedean_coalescence_exclusion", ax_map)
        self.assertIn("syracuseTreeWord_solves_one_equation", ax_map)
        self.assertIn("syracuseTreeVal_injective", ax_map)
        self.assertIn("syracuseTreeVal_upper_bound", ax_map)
        self.assertGreaterEqual(res["theorems_audited"], 480)
        self.assertGreaterEqual(res["axiom_free_theorem_count"], 155)
        self.assertIn("minimal_counterexample_mod36_in_5_classes", ax_map)
        self.assertIn("collatz_standard_iff_backward_carry_window", ax_map)
        self.assertIn("collatz_standard_iff_multi_root_forest_collision", ax_map)
        self.assertIn("collatz_standard_iff_sieved_backward_carry_window", ax_map)
        self.assertIn("collatz_standard_iff_sieved_forest_collision", ax_map)
        self.assertIn("s_low_top_strip_upper_bound", ax_map)
        self.assertFalse(res["timed_out"])

    def test_lean4_kernel_verification_timeout_budget_and_graceful_handling(self) -> None:
        import contextlib
        import io
        import subprocess
        from unittest import mock
        from collatz_analysis import formal_proofs as fp
        from collatz_analysis.cli import main as cli_main

        # 1. Invalid timeout_sec values must raise ValueError deterministically (even if cache warm)
        for bad_to in (0, 0.0, -0.5, -30, float("nan"), float("inf"), float("-inf"), False, True):
            with self.assertRaises(ValueError):
                verify_lean4_kernel_proofs(timeout_sec=bad_to)  # type: ignore[arg-type]

        # 2. Remaining timeout_sec propagates to lean --version, lake --no-build build,
        #    lake build <target>, and lean CollatzFormalAudit.lean (never hardcoded 30.0s!)
        observed_timeouts_900: list[tuple[str, float]] = []

        def fake_run_900(cmd: list[str], **kwargs: object) -> subprocess.CompletedProcess[str]:
            to_val = float(kwargs["timeout"])  # type: ignore[arg-type]
            observed_timeouts_900.append((" ".join(cmd[1:3]), to_val))
            if cmd[1:2] == ["--version"]:
                return subprocess.CompletedProcess(cmd, 0, stdout="Lean (version 4.35.0)\n", stderr="")
            if "--no-build" in cmd:
                return subprocess.CompletedProcess(cmd, 0, stdout="", stderr="")
            return subprocess.CompletedProcess(cmd, 1, stdout="", stderr="synthetic audit stop")

        with mock.patch("collatz_analysis.formal_proofs.subprocess.run", side_effect=fake_run_900):
            r900 = verify_lean4_kernel_proofs(timeout_sec=900.0, bypass_cache=True)
        self.assertFalse(r900["timed_out"])
        self.assertFalse(r900["pure_kernel_verified"])
        self.assertEqual(len(observed_timeouts_900), 3)
        for stage_tag, to_val in observed_timeouts_900:
            self.assertGreater(
                to_val,
                850.0,
                f"Expected full remaining 900s budget (not 30s cap) at {stage_tag}, got {to_val}",
            )

        observed_timeouts_small: list[float] = []

        def fake_run_small(cmd: list[str], **kwargs: object) -> subprocess.CompletedProcess[str]:
            to_val = float(kwargs["timeout"])  # type: ignore[arg-type]
            observed_timeouts_small.append(to_val)
            if cmd[1:2] == ["--version"]:
                return subprocess.CompletedProcess(cmd, 0, stdout="Lean (version 4.35.0)\n", stderr="")
            if "--no-build" in cmd:
                return subprocess.CompletedProcess(cmd, 3, stdout="", stderr="")
            if "build" in cmd:
                return subprocess.CompletedProcess(cmd, 0, stdout="", stderr="")
            return subprocess.CompletedProcess(cmd, 1, stdout="", stderr="stop audit")

        with mock.patch("collatz_analysis.formal_proofs.subprocess.run", side_effect=fake_run_small):
            r_small = verify_lean4_kernel_proofs(timeout_sec=12.5, bypass_cache=True)
        self.assertFalse(r_small["timed_out"])
        self.assertEqual(len(observed_timeouts_small), 2 + len(fp._LAKE_SEQUENTIAL_TARGETS) + 1)
        for to_val in observed_timeouts_small:
            self.assertGreater(to_val, 0.0)
            self.assertLessEqual(to_val, 12.5)

        # 2b. When Stage 3 (lake build <target>) fails with non-zero exit code, Stage 4 is skipped
        #     (never running lean on broken concatenated multi-module source!) and None streams are safe
        calls_lake_fail: list[list[str]] = []

        def fake_lake_fail(cmd: list[str], **kwargs: object) -> subprocess.CompletedProcess[str]:
            calls_lake_fail.append(cmd)
            if cmd[1:2] == ["--version"]:
                return subprocess.CompletedProcess(cmd, 0, stdout="Lean (version 4.35.0)\n", stderr="")
            if "--no-build" in cmd:
                return subprocess.CompletedProcess(cmd, 3, stdout=None, stderr=None)  # type: ignore[arg-type]
            if "build" in cmd:
                return subprocess.CompletedProcess(
                    cmd, 1, stdout=None, stderr="real Core.lean compile failure"  # type: ignore[arg-type]
                )
            return subprocess.CompletedProcess(cmd, 1, stdout="", stderr="SHOULD_NOT_RUN_STAGE4")

        with mock.patch("collatz_analysis.formal_proofs.subprocess.run", side_effect=fake_lake_fail):
            r_lake_fail = verify_lean4_kernel_proofs(timeout_sec=20.0, bypass_cache=True)
        self.assertEqual(len(calls_lake_fail), 3)
        self.assertFalse(r_lake_fail["timed_out"])
        self.assertEqual(r_lake_fail["returncode"], 1)
        self.assertFalse(r_lake_fail["pure_kernel_verified"])
        self.assertEqual(r_lake_fail["stderr"], "real Core.lean compile failure")

        # 3. Stage-by-stage TimeoutExpired handling (including raw non-UTF8 bytes on TimeoutExpired)
        # 3a) Timeout on Stage 1 (lean --version) aborts immediately without spawning lake/lean audit
        calls_s1 = 0

        def fake_to_stage1(cmd: list[str], **kwargs: object) -> subprocess.CompletedProcess[str]:
            nonlocal calls_s1
            calls_s1 += 1
            raise subprocess.TimeoutExpired(
                cmd=cmd,
                timeout=float(kwargs["timeout"]),  # type: ignore[arg-type]
                output=b"partial-ver\n",
                stderr=b"lean version probe stalled\xff\n",
            )

        with mock.patch("collatz_analysis.formal_proofs.subprocess.run", side_effect=fake_to_stage1):
            res_s1 = verify_lean4_kernel_proofs(timeout_sec=45.0, bypass_cache=True)
        self.assertEqual(calls_s1, 1)
        self.assertTrue(res_s1["timed_out"])
        self.assertEqual(res_s1["returncode"], 124)
        self.assertEqual(res_s1["lean_version"], "")
        self.assertFalse(res_s1["zero_sorry_verified"])
        self.assertFalse(res_s1["zero_warnings_verified"])
        self.assertFalse(res_s1["pure_kernel_verified"])
        self.assertIn("during lean --version", str(res_s1["stderr"]))
        self.assertIn("lean version probe stalled", str(res_s1["stderr"]))

        # 3b) Timeout on Stage 2 (lake --no-build build) aborts without spawning 56 lake targets
        calls_s2 = 0

        def fake_to_stage2(cmd: list[str], **kwargs: object) -> subprocess.CompletedProcess[str]:
            nonlocal calls_s2
            calls_s2 += 1
            if calls_s2 == 1:
                return subprocess.CompletedProcess(cmd, 0, stdout="Lean (version 4.35.0)\n", stderr="")
            raise subprocess.TimeoutExpired(
                cmd=cmd,
                timeout=float(kwargs["timeout"]),  # type: ignore[arg-type]
                output=None,
                stderr="lake trace check timed out",
            )

        with mock.patch("collatz_analysis.formal_proofs.subprocess.run", side_effect=fake_to_stage2):
            res_s2 = verify_lean4_kernel_proofs(timeout_sec=60.0, bypass_cache=True)
        self.assertEqual(calls_s2, 2)
        self.assertTrue(res_s2["timed_out"])
        self.assertEqual(res_s2["returncode"], 124)
        self.assertFalse(res_s2["pure_kernel_verified"])
        self.assertIn("during lake --no-build build", str(res_s2["stderr"]))
        self.assertIn("lake trace check timed out", str(res_s2["stderr"]))

        # 3c) Timeout on Stage 3 (lake build +CollatzFormal.Core) stops target loop immediately
        calls_s3 = 0

        def fake_to_stage3(cmd: list[str], **kwargs: object) -> subprocess.CompletedProcess[str]:
            nonlocal calls_s3
            calls_s3 += 1
            if calls_s3 == 1:
                return subprocess.CompletedProcess(cmd, 0, stdout="Lean (version 4.35.0)\n", stderr="")
            if calls_s3 == 2:
                return subprocess.CompletedProcess(cmd, 3, stdout="", stderr="")
            raise subprocess.TimeoutExpired(
                cmd=cmd,
                timeout=float(kwargs["timeout"]),  # type: ignore[arg-type]
                output="building Core...",
                stderr="",
            )

        with mock.patch("collatz_analysis.formal_proofs.subprocess.run", side_effect=fake_to_stage3):
            res_s3 = verify_lean4_kernel_proofs(timeout_sec=60.0, bypass_cache=True)
        self.assertEqual(calls_s3, 3)
        self.assertTrue(res_s3["timed_out"])
        self.assertEqual(res_s3["returncode"], 124)
        self.assertFalse(res_s3["pure_kernel_verified"])
        self.assertIn("during lake build +CollatzFormal.Core", str(res_s3["stderr"]))

        # 3d) Timeout on Stage 4 (lean CollatzFormalAudit.lean) with >20 partial stdout lines
        calls_s4 = 0
        long_partial_out = "\n".join(f"line-{idx}" for idx in range(30))

        def fake_to_stage4(cmd: list[str], **kwargs: object) -> subprocess.CompletedProcess[str]:
            nonlocal calls_s4
            calls_s4 += 1
            if calls_s4 == 1:
                return subprocess.CompletedProcess(cmd, 0, stdout="Lean (version 4.35.0)\n", stderr="")
            if calls_s4 == 2:
                return subprocess.CompletedProcess(cmd, 0, stdout="", stderr="")
            raise subprocess.TimeoutExpired(
                cmd=cmd,
                timeout=float(kwargs["timeout"]),  # type: ignore[arg-type]
                output=long_partial_out,
                stderr="kernel elaboration exceeded budget",
            )

        with mock.patch("collatz_analysis.formal_proofs.subprocess.run", side_effect=fake_to_stage4):
            res_s4 = verify_lean4_kernel_proofs(timeout_sec=60.0, bypass_cache=True)
        self.assertEqual(calls_s4, 3)
        self.assertTrue(res_s4["timed_out"])
        self.assertEqual(res_s4["returncode"], 124)
        self.assertEqual(res_s4["theorems_audited"], 0)
        self.assertFalse(res_s4["zero_sorry_verified"])
        self.assertFalse(res_s4["zero_warnings_verified"])
        self.assertFalse(res_s4["pure_kernel_verified"])
        self.assertIn("during lean CollatzFormalAudit.lean", str(res_s4["stderr"]))
        self.assertIn("kernel elaboration exceeded budget", str(res_s4["stderr"]))
        self.assertNotIn("line-0\n", str(res_s4["stderr"]))
        self.assertIn("line-29", str(res_s4["stderr"]))

        # 4. Pre-stage deadline exhaustion (rem <= 0 before spawning next subprocess)
        fake_clock = [100.0, 100.1, 106.0, 106.1]

        def step_clock() -> float:
            return fake_clock.pop(0) if len(fake_clock) > 1 else fake_clock[0]

        with mock.patch("collatz_analysis.formal_proofs.time.perf_counter", side_effect=step_clock), mock.patch(
            "collatz_analysis.formal_proofs.subprocess.run",
            return_value=subprocess.CompletedProcess(["lean", "--version"], 0, stdout="Lean 4.35.0\n", stderr=""),
        ) as run_mock:
            res_exhausted = verify_lean4_kernel_proofs(timeout_sec=5.0, bypass_cache=True)
        self.assertEqual(run_mock.call_count, 1)
        self.assertTrue(res_exhausted["timed_out"])
        self.assertEqual(res_exhausted["returncode"], 124)
        self.assertFalse(res_exhausted["pure_kernel_verified"])
        self.assertIn("Timeout budget (5.000s) exhausted before", str(res_exhausted["stderr"]))

        # 5. Live end-to-end tiny-timeout check: never raises unhandled TimeoutExpired and never
        #    poisons _LEAN4_AUDIT_CACHE for subsequent normal calls
        saved_cache = dict(fp._LEAN4_AUDIT_CACHE)
        try:
            fp._LEAN4_AUDIT_CACHE.clear()
            live_to = verify_lean4_kernel_proofs(timeout_sec=0.001, bypass_cache=True)
            self.assertTrue(live_to["timed_out"])
            self.assertEqual(live_to["returncode"], 124)
            self.assertFalse(live_to["pure_kernel_verified"])
            self.assertEqual(len(fp._LEAN4_AUDIT_CACHE), 0)
        finally:
            fp._LEAN4_AUDIT_CACHE.clear()
            fp._LEAN4_AUDIT_CACHE.update(saved_cache)

        # 6. CLI --summary handles timed-out kernel audit cleanly with exit code 1 & diagnostic line
        buf_cli = io.StringIO()
        with mock.patch(
            "collatz_analysis.cli.verify_lean4_kernel_proofs",
            return_value=res_s2,
        ), contextlib.redirect_stdout(buf_cli):
            rc_cli = cli_main(["--summary", "--dp-depth", "10"])
        self.assertEqual(rc_cli, 1)
        self.assertIn("Kernel audit diagnostics", buf_cli.getvalue())
        self.assertIn("Timed out after", buf_cli.getvalue())

        # 7. Missing Lean binary path includes timed_out == False cleanly
        with mock.patch("collatz_analysis.formal_proofs.find_lean4_executable", return_value=None):
            res_nolean = verify_lean4_kernel_proofs(timeout_sec=10.0, bypass_cache=True)
        self.assertFalse(res_nolean["lean_available"])
        self.assertFalse(res_nolean["timed_out"])
        self.assertFalse(res_nolean["pure_kernel_verified"])

        # 8. Missing Lake binary on multi-module package refuses to trust potentially stale .olean files
        with mock.patch("collatz_analysis.formal_proofs.find_lake_executable", return_value=None):
            res_nolake = verify_lean4_kernel_proofs(timeout_sec=15.0, bypass_cache=True)
        self.assertIsNone(res_nolake["lake_executable"])
        self.assertFalse(res_nolake["timed_out"])
        self.assertEqual(res_nolake["returncode"], 1)
        self.assertFalse(res_nolake["zero_sorry_verified"])
        self.assertFalse(res_nolake["zero_warnings_verified"])
        self.assertFalse(res_nolake["pure_kernel_verified"])
        self.assertIn("Lake executable not found", str(res_nolake["stderr"]))

        # 9. Live _run_process_tree_bounded safely decodes raw non-UTF-8 bytes (0xff) without UnicodeDecodeError
        import sys
        import time
        from pathlib import Path

        cp_nonutf8 = fp._run_process_tree_bounded(
            [
                sys.executable,
                "-c",
                "import sys; sys.stdout.buffer.write(b'ok\\xffout\\n'); sys.stderr.buffer.write(b'err\\xfe\\n')",
            ],
            cwd=str(Path(__file__).resolve().parent),
            env=None,
            timeout=10.0,
        )
        self.assertEqual(cp_nonutf8.returncode, 0)
        self.assertIn("ok\ufffdout", cp_nonutf8.stdout)
        self.assertIn("err\ufffd", cp_nonutf8.stderr)

        # 10. Live _run_process_tree_bounded kills grandchild processes holding inherited stdout/stderr pipes
        #     immediately on timeout (returning well below the 8.0s grandchild sleep)
        parent_spawn_code = (
            "import subprocess, sys, time; "
            "subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(8)']); "
            "print('partial-before-timeout', flush=True); "
            "time.sleep(8)"
        )
        t_start = time.perf_counter()
        with self.assertRaises(subprocess.TimeoutExpired) as cm_tree:
            fp._run_process_tree_bounded(
                [sys.executable, "-c", parent_spawn_code],
                cwd=str(Path(__file__).resolve().parent),
                env=None,
                timeout=0.4,
            )
        dt_tree = time.perf_counter() - t_start
        self.assertLess(
            dt_tree,
            5.0,
            f"Grandchild pipe inheritance delayed TimeoutExpired to {dt_tree:.3f}s (expected < 5.0s for 8s grandchild)",
        )
        self.assertIn("partial-before-timeout", fp._decode_proc_stream(cm_tree.exception.stdout))

    def test_theorem_23_minimal_counterexample_rigidity_and_sturmian_obstruction(self) -> None:
        res = verify_minimal_counterexample_rigidity_and_sturmian_obstruction(
            max_k_cone=14, sturm_depth=30
        )
        self.assertTrue(res["mod4_eq_3_and_w1_ge_2_verified"])
        self.assertTrue(res["first_even_run_a1_eq_1_entry_merger_verified"])
        self.assertEqual(res["unique_odd_multiplier_merger_pairs"], [(3, 5)])
        self.assertTrue(res["q3_r5_uniqueness_verified"])
        self.assertTrue(res["counter_model_M3_13_escapes_entry_merger"])
        self.assertTrue(res["counter_model_M1_19_5_merges_with_7_5"])
        self.assertTrue(res["raney_S_equals_full_end_expanding_E"])
        self.assertTrue(res["suffix_reduction_verified"])
        self.assertEqual(res["max_target_kp"], 18)
        self.assertEqual(res["complete_all_wp_sturm_depth"], 19)
        self.assertEqual(res["surviving_targets_indexed"], 16740)
        self.assertTrue(res["sturmian_w1_w2_universal_obstruction_verified"])
        self.assertTrue(res["pure_2_3_adic_coalescence_falsified_on_S_infty"])
        self.assertEqual(res["neg_cycle_contractive_coalescences"], {-1: 0, -5: 0, -17: 0})
        self.assertEqual(res["sturmian_contractive_coalescences"], 0)

        # Sturmian check up to depth 45 across all targets up to k' <= 18 (complete for k <= 19):
        res_45 = verify_minimal_counterexample_rigidity_and_sturmian_obstruction(
            max_k_cone=8, sturm_depth=45, max_target_kp=18
        )
        self.assertEqual(res_45["complete_all_wp_sturm_depth"], 19)
        self.assertEqual(res_45["sturmian_contractive_coalescences"], 0)

        # Boundary checks:
        # 1) n = 1 (excluded by n > 1) has T^2(1) = 1 (not < 1), whereas n = 2, 4, 5 drop < n in <= 2 steps:
        self.assertEqual(collatz_compressed_step(collatz_compressed_step(1)), 1)
        for n_small in (2, 4, 5):
            t1 = collatz_compressed_step(n_small)
            t2 = collatz_compressed_step(t1)
            self.assertTrue(t1 < n_small or t2 < n_small)
        # 2) a_1 = 1 boundary (x = 7: w_1 = 3, a_1 = 1) does NOT satisfy T^{w_1+1}((x-1)/2) == T^{w_1+2}(x),
        #    whereas a_1 >= 2 (x = 15: w_1 = 4, a_1 = 4 >= 2) DOES merge at T^5(7) == T^6(15) == 20:
        t4_of_3 = 3
        for _ in range(4):
            t4_of_3 = collatz_compressed_step(t4_of_3)
        t5_of_7 = 7
        for _ in range(5):
            t5_of_7 = collatz_compressed_step(t5_of_7)
        self.assertNotEqual(t4_of_3, t5_of_7)
        t6_of_15 = 15
        for _ in range(6):
            t6_of_15 = collatz_compressed_step(t6_of_15)
        self.assertEqual(t5_of_7, 20)
        self.assertEqual(t6_of_15, 20)

    def test_theorem_24_cyclic_shift_collapse_and_reflective_m92_certificate(self) -> None:
        res = verify_cyclic_shift_carry_collapse_and_reflective_hensel(max_k_shift=10)
        self.assertTrue(res["cyclic_shift_polynomial_identity_verified"])
        self.assertTrue(res["cyclic_shift_gcd_collapse_verified"])
        self.assertTrue(res["m2_neg17_all_11_shifts_div_by_139"])
        self.assertTrue(res["m3_5n1_13_all_7_shifts_div_by_3"])
        self.assertTrue(res["m_uniform_cyclic_shift_ppd_falsified"])
        self.assertEqual(res["m92_reflective_certificate"]["band_count"], 61)
        self.assertTrue(res["m92_reflective_certificate"]["zero_survivors_verified"])
        self.assertTrue(res["lean_m92_bands_exact_match"])

        m92_full = generate_m92_reflective_hensel_bands(N0=1 << 71)
        bands = m92_full["bands"]
        self.assertEqual(len(bands), 61)
        self.assertEqual(len(m92_full["no_odd_mul_bands"]), 4)
        self.assertEqual(m92_full["low_k1_max"], 8)
        self.assertEqual(m92_full["high_k1_min"], 74)
        self.assertEqual(sum(len(b.k2_stops) for b in bands), 1120)
        self.assertTrue(all(k2_m == k2_s for b in bands for k2_m, k2_s in b.k2_stops))

        # Explicit error-path check: unsupported N0 != 2^71 must raise ValueError
        with self.assertRaises(ValueError):
            generate_m92_reflective_hensel_bands(N0=1 << 70)

        # Boundary check on empty word v = () and unit cycle v = (1, 0):
        k_empty, w_empty, c_empty = affine_parameters(())
        self.assertEqual((k_empty, w_empty, c_empty), (0, 0, 0))
        k_u, w_u, c_u = affine_parameters((1, 0))
        self.assertEqual((1 << k_u) - (3**w_u), 1)
        self.assertEqual(c_u, 1)

    def test_theorem_24b_hensel_r_lt_max_r_regression_and_windowed_partition(self) -> None:
        # 1) Adversarial regression test for _run_hensel_root_chunk when a genuine exit
        #    occurs at intermediate depth r = 1 < max_r with k_exp < k_coll <= k_exp + kd_exit:
        k1 = 20
        u1 = ((3 * (1 << 21) - 1) * pow(3**k1, -1, 1 << 23)) % (1 << 23)
        self.assertEqual(u1 & 1, 1)
        z1 = (1 << k1) * u1 - 1
        z2 = ((3**k1) * u1 - 1) // 2
        self.assertEqual(z2 & 1, 1)
        k2 = ((z2 + 1) & -(z2 + 1)).bit_length() - 1
        self.assertEqual(k2, 20)
        u2 = (z2 + 1) >> k2
        self.assertEqual(u2 & 3, 3)
        z3 = ((3**k2) * u2 - 1) // 2
        self.assertEqual(z3 & 1, 1)
        b1_val = z2 - 1000
        b2_val = 400 * z2
        self.assertTrue(b1_val + 1 <= z2 <= b2_val)
        self.assertGreaterEqual(z3, b2_val + 1)
        lo1 = max(1, z1 - (1 << 33))
        hi1 = z1 + (1 << 33)
        n0_threshold = z1 - 10
        max_bl = b2_val.bit_length() + 16
        kd_b1 = _build_kd_threshold_table(2 * (b1_val + 1) + 1, max_bl)
        kd_b2 = _build_kd_threshold_table(2 * (b2_val + 1) + 1, max_bl)
        for max_r_test in (1, 2, 3):
            _, _, survs = _run_hensel_root_chunk(
                (n0_threshold, b1_val, b2_val, max_r_test, [(k1, lo1, hi1, u1, u1)], kd_b1, kd_b2)
            )
            self.assertIn(
                z1,
                survs,
                f"_run_hensel_root_chunk dropped genuine r=1 exit z1={z1} at max_r={max_r_test}",
            )

        # 2) Direct verification of _certify_windowed_exact_r_subcase & _run_windowed_hensel_chunk
        #    (both serial max_workers=1 and parallel ProcessPoolExecutor max_workers=2) on m = 93, u = 1:
        N0 = 1 << 71
        b1_93 = 83847751484210778428629
        b2_93 = 59008949650485003215843958947717464
        lo_93 = N0 + 1
        bands_93_s1 = []
        for k_band in (42, 43, 44, 45):
            u_min = (lo_93 + (1 << k_band)) >> k_band
            if (u_min & 1) == 0:
                u_min += 1
            u_max = (b1_93 + 1) >> k_band
            if (u_max & 1) == 0:
                u_max -= 1
            bands_93_s1.append((k_band, lo_93, b1_93, u_min, u_max))
        self.assertEqual(len(bands_93_s1), 4)

        split_93 = (1 << 80) - 1
        window_cases_93 = [
            (((split_93 + 1, b2_93), (split_93 + 1, b2_93)), bands_93_s1),
            (((b1_93 + 1, split_93), (b1_93 + 1, b2_93)), bands_93_s1),
            (((split_93 + 1, b2_93), (b1_93 + 1, split_93)), bands_93_s1),
        ]
        sub_s = _certify_windowed_exact_r_subcase(
            N0=N0,
            m=93,
            u_mult=1,
            clamped_c=2,
            b1_val=b1_93,
            b2_val=b2_93,
            window_cases=window_cases_93,
            s_regime="s=1 (r=2 windowed)",
            max_workers=1,
        )
        sub_p = _certify_windowed_exact_r_subcase(
            N0=N0,
            m=93,
            u_mult=1,
            clamped_c=2,
            b1_val=b1_93,
            b2_val=b2_93,
            window_cases=window_cases_93,
            s_regime="s=1 (r=2 windowed)",
            max_workers=2,
        )
        self.assertEqual(sub_s.cycle_survivors, 0)
        self.assertEqual(sub_p.cycle_survivors, 0)
        self.assertEqual(len(sub_s.arithmetic_survivors), 99)
        self.assertEqual(sub_s.arithmetic_survivors, sub_p.arithmetic_survivors)
        self.assertGreater(sub_s.tree_nodes, 0)
        self.assertGreater(sub_s.leaf_congruences, 0)
        self.assertEqual(sub_s.tree_nodes, sub_p.tree_nodes)
        self.assertEqual(sub_s.leaf_congruences, sub_p.leaf_congruences)

        # 3) Cross-check exact survivor detection between _certify_windowed_exact_r_subcase,
        #    _certify_single_hensel_subcase, and Lean 4's m93U1S2Band45 on m = 93, u = 1, s >= 2, k1 = 45:
        m93_u1_b1 = 186580408057834147634799
        m93_u1_b2 = 3823138529586028419141319555512320798
        band_45 = [(45, 11235001557289826002597, m93_u1_b1, 319317951, 5302934143)]
        sub_45_win = _certify_windowed_exact_r_subcase(
            N0=N0,
            m=93,
            u_mult=1,
            clamped_c=1,
            b1_val=m93_u1_b1,
            b2_val=m93_u1_b2,
            window_cases=[(((m93_u1_b1 + 1, m93_u1_b2),), band_45)],
            s_regime="s>=2 (r=1 windowed)",
            max_workers=1,
        )
        sub_45_std = _certify_single_hensel_subcase(
            N0=N0,
            m=93,
            u_mult=1,
            clamped_c=2,
            b1_val=m93_u1_b1,
            b2_val=m93_u1_b2,
            bands=band_45,
            max_r=1,
            s_regime="s>=2",
            max_workers=1,
        )
        self.assertEqual(sub_45_win.arithmetic_survivors, (179507528690102354051071,))
        self.assertEqual(sub_45_std.arithmetic_survivors, (179507528690102354051071,))
        self.assertEqual(sub_45_win.cycle_survivors, 0)
        self.assertEqual(sub_45_std.cycle_survivors, 0)

        # 4) Boundary / error-path checks on prove_m95_all_weight_nonexistence:
        with self.assertRaises(ValueError):
            prove_m95_all_weight_nonexistence(N0=1)
        with self.assertRaises(ValueError):
            prove_m95_all_weight_nonexistence(N0=1 << 68)

    def test_theorem_25_one_equation_horizon_families_and_counter_model_matrix(self) -> None:
        res = verify_one_equation_parametric_families_and_density_obstruction(
            max_k_word_audit=11, coverage_limit_x=5000, max_weight_w0=4
        )
        self.assertTrue(res["nonpos_solution_exclusion_verified"])
        self.assertTrue(res["universal_pow4_horizon_verified"])
        self.assertTrue(res["parametric_families_verified"])
        self.assertTrue(res["polylog_binomial_bound_verified"])
        self.assertTrue(res["bounded_weight_covering_congruences_falsified"])

        # Boundary checks:
        # 1) Repeated trivial-cycle word v = (1, 0)^r (for r = 0..6, including empty word r = 0)
        #    solves 2^{2r} = 3^r * 1 + C(v) with SHARP equality 2^{|v|} == 4^{w(v)} * 1:
        for r in range(7):
            v_rep = (1, 0) * r
            k_r, w_r, c_r = affine_parameters(v_rep)
            self.assertEqual(1 << k_r, (3**w_r) * 1 + c_r)
            self.assertEqual(1 << k_r, (4**w_r) * 1)
        # 2) W_0 = 0 covers ONLY powers of 2 <= 5000 (2^0 .. 2^12 = 4096 -> exactly 13 integers):
        self.assertEqual(res["coverage_by_w0"][0]["covered_count"], 13)

        # Master 3x3 counter-model discrimination matrix:
        mat = verify_boost_three_line_counter_model_matrix()
        self.assertTrue(mat["all_counter_models_discriminated"])
        self.assertEqual(mat["surviving_count"], 3)
        self.assertEqual(mat["falsified_count"], 3)
        self.assertEqual(len(mat["audit_matrix"]), 6)

    def test_theorem_26_zero_trust_gap_rational_log_and_m92_pipeline(self) -> None:
        res = verify_zero_trust_gap_rational_log_and_m92_pipeline(N0=1 << 71)
        self.assertTrue(res["taylor_intervals_sound"])
        self.assertLessEqual(res["taylor_ln2_width_at_2_pow_200"], 70)
        self.assertLessEqual(res["taylor_ln3_width_at_2_pow_200"], 110)
        self.assertEqual(res["convergents_52_count"], 52)
        self.assertTrue(res["convergents_52_unimodular"])
        self.assertTrue(res["convergents_52_alternating_certified"])
        self.assertTrue(res["m92_derived_bands_subsumed_9_to_73"])
        self.assertTrue(res["counter_models_discriminated"])

        # Boundary checks at k1 = 8 and k1 = 74 matching CollatzFormal.lean:
        m92_glob_hi1 = 11954868071481462849280
        exact_m92_b1 = 186580408057834151310020
        self.assertLess((3**8) * (m92_glob_hi1 + 1), (1 << 8) * (2 * (exact_m92_b1 + 1) + 1))
        self.assertLess(m92_glob_hi1 + 1, 1 << 74)

        with self.assertRaises(ValueError):
            verify_zero_trust_gap_rational_log_and_m92_pipeline(N0=1 << 68)

    def test_theorem_26b_m96_to_m98_hensel_frontier_and_c23_acceleration(self) -> None:
        res = prove_m96_m98_hensel_frontier(
            N0=1 << 71,
            max_m_full=96,
            eliminate_higher_multiples_up_to_m=98,
            max_workers=1,
            pairs_override=[(96, 3), (96, 4), (97, 4), (98, 6)],
        )
        self.assertTrue(res["zero_cycle_survivors_verified"])
        self.assertEqual(res["total_cycle_survivors"], 0)
        self.assertGreater(res["total_tree_nodes"], 0)
        self.assertGreater(res["total_leaf_congruences"], 0)
        self.assertTrue(res["lean_kernel_survivor_coverage_verified"])

        # Verify all 8,075 Lean 4 survivor list entries directly in Python:
        from collatz_analysis.formal_proofs import read_all_collatz_lean_sources

        lean_src = read_all_collatz_lean_sources()
        self.assertIn("all_new_m96_to_98_hensel_survivors_drop_below_2_pow_71", lean_src)
        self.assertIn("no_nontrivial_spiral_cycles_1_to_92", lean_src)
        pairs_96_98 = []
        for m_blk in re.finditer(r"def henselSurvivors96To98\w*\s*:.*?=\s*\[(.*?)\]", lean_src, re.S):
            for z_s, k_s in re.findall(r"\((\d+)\s*,\s*(\d+)\)", m_blk.group(1)):
                pairs_96_98.append((int(z_s), int(k_s)))
        self.assertEqual(len(pairs_96_98), 8075)
        n0_barina = 1 << 71
        for z_val, k_steps in pairs_96_98:
            self.assertGreater(z_val, n0_barina)
            self.assertEqual(z_val & 1, 1)
            cur = z_val
            rem = k_steps
            while rem > 0:
                if (cur & 1) == 0:
                    tz = min(rem, (cur & -cur).bit_length() - 1)
                    cur >>= tz
                    rem -= tz
                else:
                    tz = min(rem, ((cur + 1) & -(cur + 1)).bit_length() - 1)
                    cur = (3**tz) * ((cur + 1) >> tz) - 1
                    rem -= tz
            self.assertLessEqual(cur, n0_barina)

        # Error-path checks:
        with self.assertRaises(ValueError):
            prove_m96_m98_hensel_frontier(N0=1)
        with self.assertRaises(ValueError):
            prove_m96_m98_hensel_frontier(max_m_full=91)
        with self.assertRaises(ValueError):
            prove_m96_m98_hensel_frontier(max_m_full=100)
        with self.assertRaises(ValueError):
            prove_m96_m98_hensel_frontier(max_m_full=96, eliminate_higher_multiples_up_to_m=95)
        with self.assertRaises(ValueError):
            prove_m96_m98_hensel_frontier(pairs_override=[(90, 1)])

    def test_theorem_27_multiblock_rigidity_and_archimedean_coupling(self) -> None:
        res = verify_multiblock_rigidity_and_archimedean_coupling(
            max_sample_odd=1025, max_k_surv=14
        )
        self.assertTrue(res["subdouble_entry_merger_verified"])
        self.assertTrue(res["subquad_exit_tail_merger_verified"])
        self.assertTrue(res["block1_u1_mod4_rigidity_verified"])
        self.assertTrue(res["block2_w1_2_or_3_forces_a2_eq_1_verified"])
        self.assertTrue(res["six_block_w2_subdouble_verified"])
        self.assertTrue(res["block2_w1_4_w2_1_forces_a2_eq_1_verified"])
        self.assertTrue(res["cantor_cone_1w_00_family_verified"])
        self.assertTrue(res["surviving_carry_bound_verified"])
        self.assertTrue(res["three_adic_fiber_ceiling_verified"])
        self.assertTrue(res["counter_models_discriminated"])

        # Boundary check: w = 4 survives 1^4 0^2 (81 > 64), whereas w = 3 fails 1^3 0^2 (27 < 32):
        self.assertTrue(is_coefficient_surviving_prefix((1, 1, 1, 1, 0, 0)))
        self.assertFalse(is_coefficient_surviving_prefix((1, 1, 1, 0, 0)))

        with self.assertRaises(ValueError):
            verify_multiblock_rigidity_and_archimedean_coupling(max_sample_odd=5)
        with self.assertRaises(ValueError):
            verify_multiblock_rigidity_and_archimedean_coupling(max_k_surv=2)

    def test_theorem_28_unbounded_syracuse_predecessor_tree_growth(self) -> None:
        res = verify_unbounded_syracuse_predecessor_tree_growth(max_depth_w=10)
        self.assertEqual(res["total_tree_nodes_verified"], 2047)
        self.assertEqual(res["distinct_values_count"], 2047)
        self.assertTrue(res["garden_of_eden_bypass_invariant_verified"])
        self.assertTrue(res["one_equation_identity_verified"])
        self.assertTrue(res["global_injectivity_verified"])
        self.assertTrue(res["exponential_upper_bound_verified"])
        self.assertGreater(res["asymptotic_growth_exponent"], 0.226)
        self.assertLess(res["asymptotic_growth_exponent"], 0.227)
        self.assertTrue(res["counter_models_discriminated"])

        # Boundary depth = 1 check (1 + 2 = 3 nodes):
        res1 = verify_unbounded_syracuse_predecessor_tree_growth(max_depth_w=1)
        self.assertEqual(res1["distinct_values_count"], 3)

        with self.assertRaises(ValueError):
            verify_unbounded_syracuse_predecessor_tree_growth(max_depth_w=0)
        with self.assertRaises(ValueError):
            verify_unbounded_syracuse_predecessor_tree_growth(max_depth_w=20)

    def test_theorem_29_general_backward_merger_and_bit_exhaustion(self) -> None:
        res = verify_general_backward_merger_and_bit_exhaustion(
            max_word_len=6, max_sieve_b=6, max_n_sample=240
        )
        self.assertTrue(res["universal_affine_converse_verified"])
        self.assertGreater(res["universal_converse_pairs_checked"], 100)
        self.assertTrue(res["carry_pos_nondiv3_verified"])
        self.assertTrue(res["n_min_mod3_ne_2_verified"])
        self.assertTrue(res["n_min_mod12_confined_to_3_and_7"])
        self.assertTrue(res["n_min_mod9_ne_4_via_u110_verified"])
        self.assertTrue(res["sub_3_2_and_sub_9_4_mergers_verified"])
        self.assertTrue(res["initial_bit_exhaustion_verified"])
        self.assertGreater(res["initial_bit_exhaustion_samples"], 10)
        self.assertTrue(res["all_zero_mod3_survive_garden_of_eden"])
        self.assertTrue(res["single_return_measure_zero_falsified"])
        self.assertGreater(res["single_return_survival_density_mu1"], 0.29)
        self.assertTrue(res["n_min_mod36_confined_to_5_classes"])
        self.assertTrue(res["m1_q2_pos_19_5_and_29_5_mergers_verified"])
        self.assertTrue(res["m2_z_neg_1_5_17_mergers_verified"])
        self.assertTrue(res["m3_5n1_bounded_min_counterexample_5_max_208"])
        self.assertTrue(res["counter_models_all_three_verified"])

        # Boundary checks:
        # 1) Empty parity word u = () at negative, zero, and positive x:
        k0, w0, c0 = affine_parameters(())
        self.assertEqual((k0, w0, c0), (0, 0, 0))
        for x_val in (-17, -1, 0, 1, 7):
            self.assertEqual((1 << k0) * x_val, (3**w0) * x_val + c0)
        # 2) Boundary n = 4 (4 % 9 == 4): u = (1, 1, 0) merges n' = (8*4 - 5)//9 = 3 in 3 steps:
        self.assertEqual((8 * 4 - 5) // 9, 3)
        c3 = 3
        for _ in range(3):
            c3 = collatz_compressed_step(c3)
        self.assertEqual(c3, 4)
        # 3) Boundary x = 2 (sub-3/2) and x = 8 (sub-9/4):
        self.assertEqual(collatz_compressed_step((2 * 2 - 1) // 3), 2)
        self.assertEqual(
            collatz_compressed_step(collatz_compressed_step((4 * 8 - 5) // 9)), 8
        )

        # Error-path checks:
        with self.assertRaises(ValueError):
            verify_general_backward_merger_and_bit_exhaustion(max_word_len=0)
        with self.assertRaises(ValueError):
            verify_general_backward_merger_and_bit_exhaustion(max_sieve_b=1)
        with self.assertRaises(ValueError):
            verify_general_backward_merger_and_bit_exhaustion(max_n_sample=10)

    def test_theorem_30_multi_root_syracuse_forest_and_fourier_mixing(self) -> None:
        res = verify_multi_root_syracuse_forest_and_fourier_mixing(
            max_node_scan=1200, max_tree_depth=5, max_n_prop_check=120
        )
        self.assertTrue(res["overlap_witness_13_and_7_verified"])
        self.assertTrue(res["root_iff_indegree_zero_verified"])
        self.assertTrue(res["global_forest_injectivity_verified"])
        self.assertTrue(res["forest_upper_bound_verified"])
        self.assertTrue(res["pigeonhole_trap_at_x_eq_n_caught"])
        self.assertTrue(res["nonprimitive_fourier_decay_falsified"])
        self.assertTrue(res["primitive_fourier_decay_verified"])
        self.assertEqual(res["window_mixing_prop_verified_up_to_n"], 120)
        self.assertEqual(res["forest_collision_prop_verified_up_to_n"], 120)
        self.assertGreaterEqual(res["sieved_positive_depth_forest_collisions"], 5)
        self.assertTrue(res["m1_q2_19_5_29_5_excluded_from_forest"])
        self.assertTrue(res["m2_z_neg_1_5_17_excluded_from_window"])
        self.assertTrue(res["m3_5n1_min5_fails_window_prop"])
        self.assertTrue(res["counter_models_all_three_excluded"])

        # Boundary checks on is_syracuse_forest_root & syracuse_forest_val:
        for bad_r in (-5, 0, 1, 3, 4, 6, 7, 9, 11, 13, 15, 21, 85 * 3, 128):
            self.assertFalse(is_syracuse_forest_root(bad_r), f"Expected non-root at {bad_r}")
        for good_r in (5, 85, 341, 469, 725):
            self.assertTrue(is_syracuse_forest_root(good_r), f"Expected forest root at {good_r}")
        self.assertEqual(syracuse_forest_val(5, ()), 5)
        self.assertEqual(syracuse_forest_val(85, ()), 85)
        self.assertEqual(syracuse_forest_val(5, (False,)), 13)
        self.assertEqual(syracuse_forest_val(5, (True,)), 53)

        # Error-path checks:
        with self.assertRaises(ValueError):
            verify_multi_root_syracuse_forest_and_fourier_mixing(max_node_scan=100)
        with self.assertRaises(ValueError):
            verify_multi_root_syracuse_forest_and_fourier_mixing(max_tree_depth=2)
        with self.assertRaises(ValueError):
            verify_multi_root_syracuse_forest_and_fourier_mixing(max_n_prop_check=10)

    def test_theorem_31_prime_denom_rigidity_and_two_vertex_hensel(self) -> None:
        res = verify_prime_denom_rigidity_and_two_vertex_frontier(
            N0=1 << 71, max_r_upper_cert=2
        )
        self.assertTrue(res["m1_q2_19_5_29_5_naive_2adic_falsified"])
        self.assertTrue(res["m2_neg17_139_full_group_falsified"])
        self.assertTrue(res["m3_5n1_13_17_denom_div_falsified"])
        self.assertTrue(res["weight3_mod23_odd_subgroup_falsified"])
        self.assertTrue(res["two_adic_valuation_lock_verified"])
        self.assertTrue(res["subgroup_index_divisibility_verified"])
        self.assertTrue(res["weight2_odd_subgroup_obstruction_verified"])
        self.assertTrue(res["c23_vs_python_two_vertex_bit_exact"])
        self.assertTrue(res["clamped_c_exact_6_7_8_verified"])
        self.assertTrue(res["upper_strip_certified_all_m97_99"])

        # Verify s_low == 2 vs s_low == c top-strip ratios on m = 97..99, u = 1:
        fm = res["frontier_records"]
        self.assertLess(fm[97]["s2_x1_max_ratio"], 0.88)
        self.assertLess(fm[98]["s2_x1_max_ratio"], 0.86)
        self.assertLess(fm[99]["s2_x1_max_ratio"], 0.84)
        for m_val in (97, 98, 99):
            self.assertGreater(fm[m_val]["s_ge2_max_ratio"], 0.95)
            self.assertLess(fm[m_val]["s_ge2_max_ratio"], 0.96)

        mat = verify_next_tier_boost_counter_model_matrix()
        self.assertTrue(mat["all_next_tier_mechanisms_verified"])
        self.assertEqual(mat["surviving_count"], 3)
        self.assertEqual(mat["falsified_count"], 3)
        self.assertEqual(len(mat["audit_matrix"]), 6)

        # Edge cases & adversarial regressions on run_two_vertex_hensel_bands:
        # 1) Empty band list across all 3 bridge modes and C23/Python:
        for mode in (0, 1, 2):
            for use_c_flag in (True, False):
                self.assertEqual(
                    run_two_vertex_hensel_bands(
                        100, 1000, 10000, 200, 1000, 2, mode, [], use_c=use_c_flag
                    ),
                    (0, 0, [], 0),
                )
        # 2) Degenerate band (lo1 > hi1 or u_min > u_max) returns 0 survivors cleanly:
        for use_c_flag in (True, False):
            _, _, surv_deg, rc_deg = run_two_vertex_hensel_bands(
                100, 1000, 10000, 200, 1000, 2, 1, [(3, 500, 400, 79, 51)], use_c=use_c_flag
            )
            self.assertEqual((surv_deg, rc_deg), ([], 0))

        # 3) Bit-exactness between C23 and pure-Python across modes 0, 1, 2 and max_r = 0..3:
        test_bands = []
        for k1 in range(1, 9):
            u_mn = max(1, ((102 + (1 << k1) - 1) >> k1)) | 1
            u_mx = 4002 >> k1
            if (u_mx & 1) == 0:
                u_mx -= 1
            if u_mn <= u_mx:
                test_bands.append((k1, 101, 4001, u_mn, u_mx))
        for mode in (0, 1, 2):
            for mr in (0, 1, 2, 3):
                _, _, sc, rcc = run_two_vertex_hensel_bands(
                    100, 2500, 90000, 250, 2500, mr, mode, test_bands, use_c=True
                )
                _, _, sp, rcp = run_two_vertex_hensel_bands(
                    100, 2500, 90000, 250, 2500, mr, mode, test_bands, use_c=False
                )
                self.assertEqual((rcc, rcp), (0, 0))
                self.assertEqual(sc, sp, f"Mismatch at mode={mode}, max_r={mr}")

        # 4) Regression for 328-bit (> 320-bit) inverse table & u640 arithmetic:
        mod328 = 1 << 328
        u328 = (((3 << 326) - 1) * pow(9, -1, mod328)) % mod328
        if (u328 & 1) == 0:
            u328 += mod328
        z328 = 4 * u328 - 1
        b1_328 = z328 + 1000
        b2_328 = (9 * (z328 + 1)) // 8 + 100
        band328 = [(2, z328 - 8, z328 + 8, u328 - 2, u328 + 2)]
        _, _, sc328, rc328_c = run_two_vertex_hensel_bands(
            z328 - 100, b1_328, b2_328, z328 - 50, b1_328, 1, 0, band328, use_c=True
        )
        _, _, sp328, rc328_p = run_two_vertex_hensel_bands(
            z328 - 100, b1_328, b2_328, z328 - 50, b1_328, 1, 0, band328, use_c=False
        )
        self.assertEqual((rc328_c, rc328_p), (0, 0))
        self.assertEqual(sc328, sp328)
        self.assertIn(z328, sc328)

        # 5) Regression for k1 in {215, 220, 245} (> 161 / > 243), 466-bit intermediates, & 350-bit b2:
        u215 = pow(3**215, -1, 1 << 125)
        if (((3**215 * u215 - 1) >> 125) & 1) == 0:
            u215 += 1 << 125
        z215 = (1 << 215) * u215 - 1
        band_k215 = [(215, z215 - 2, z215 + 2, u215, u215)]
        _, _, sc215, rc215_c = run_two_vertex_hensel_bands(
            1 << 71, z215 + 100, (1 << 349) - 1, z215 - 10, (1 << 349) - 1, 0, 1, band_k215, use_c=True
        )
        _, _, sp215, rc215_p = run_two_vertex_hensel_bands(
            1 << 71, z215 + 100, (1 << 349) - 1, z215 - 10, (1 << 349) - 1, 0, 1, band_k215, use_c=False
        )
        self.assertEqual((rc215_c, rc215_p), (0, 0))
        self.assertEqual(sc215, sp215)
        self.assertEqual(sc215, [z215])

        lo_k220 = (1 << 322) - 1
        hi_k220 = 3 * (1 << 322) - 1
        u_mn_220 = max(1, ((lo_k220 + 1 + (1 << 220) - 1) >> 220)) | 1
        u_mx_220 = (hi_k220 + 1) >> 220
        if (u_mx_220 & 1) == 0:
            u_mx_220 -= 1
        band_k220 = [(220, lo_k220, hi_k220, u_mn_220, u_mx_220)]
        _, _, sc220, rc220_c = run_two_vertex_hensel_bands(
            (1 << 71) + 1, hi_k220 + 100, (1 << 349) - 1,
            lo_k220, hi_k220 + 100, 0, 1, band_k220, use_c=True
        )
        _, _, sp220, rc220_p = run_two_vertex_hensel_bands(
            (1 << 71) + 1, hi_k220 + 100, (1 << 349) - 1,
            lo_k220, hi_k220 + 100, 0, 1, band_k220, use_c=False
        )
        self.assertEqual((rc220_c, rc220_p), (0, 0))
        self.assertEqual((sc220, sp220), ([], []))

        band_k245 = [(245, (1 << 245) - 1, 3 * (1 << 245) - 1, 1, 3)]
        _, _, sc245, rc245_c = run_two_vertex_hensel_bands(
            1 << 71, 1 << 247, (1 << 349) - 1, 1 << 72, 1 << 247, 0, 1, band_k245, use_c=True
        )
        _, _, sp245, rc245_p = run_two_vertex_hensel_bands(
            1 << 71, 1 << 247, (1 << 349) - 1, 1 << 72, 1 << 247, 0, 1, band_k245, use_c=False
        )
        self.assertEqual((rc245_c, rc245_p), (0, 0))
        self.assertEqual(sc245, sp245)

        # 6) Regression for 15-bit bridge-mode (cur_r = 2, mode = 2) kd_lo_bridge survivor z = 17055:
        band_br15 = [(5, 16031, 18079, 501, 565)]
        _, _, sc_br15, rc_br15_c = run_two_vertex_hensel_bands(
            100, 50000, 65534, 101, 49999, 2, 2, band_br15, use_c=True
        )
        _, _, sp_br15, rc_br15_p = run_two_vertex_hensel_bands(
            100, 50000, 65534, 101, 49999, 2, 2, band_br15, use_c=False
        )
        self.assertEqual((rc_br15_c, rc_br15_p), (0, 0))
        self.assertEqual(sc_br15, sp_br15)
        self.assertIn(17055, sc_br15)

        # 7) Deterministic max_budget abort (rc == 1) in BOTH mode 1 AND mode 0 (Direct Exit,
        # including astronomical leaf spans 2^326):
        for use_c_flag in (True, False):
            _, _, _, rc_ab = run_two_vertex_hensel_bands(
                100, 2500, 90000, 250, 2500, 3, 1, test_bands, max_budget=2, use_c=use_c_flag
            )
            self.assertEqual(rc_ab, 1)
            _, _, _, rc_ab0 = run_two_vertex_hensel_bands(
                100, 500000, 9000000, 200, 500000, 1, 0,
                [(2, 400003, 400003 + (1 << 20), 100001, 100001 + (1 << 18) + 1)],
                max_budget=5, use_c=use_c_flag,
            )
            self.assertEqual(rc_ab0, 1)
            _, _, _, rc_ab_astro = run_two_vertex_hensel_bands(
                100, 1 << 327, 1 << 330, 200, 1 << 327, 1, 0,
                [(2, (1 << 327) - 9, (1 << 328) + 3, (1 << 325) - 1, (1 << 326) + 1)],
                max_budget=5, use_c=use_c_flag,
            )
            self.assertEqual(rc_ab_astro, 1)

        # 8) Regression for > 4096 survivors (12,494) in a single wide C23 band via sub-band bisection:
        wide_band = [(2, 103, 200003, 27, 50001)]
        _, _, sc_wide, rc_wide_c = run_two_vertex_hensel_bands(
            10, 300000, 900000, 12, 300000, 0, 1, wide_band, use_c=True
        )
        _, _, sp_wide, rc_wide_p = run_two_vertex_hensel_bands(
            10, 300000, 900000, 12, 300000, 0, 1, wide_band, use_c=False
        )
        self.assertEqual((rc_wide_c, rc_wide_p), (0, 0))
        self.assertEqual(len(sc_wide), 12494)
        self.assertEqual(sc_wide, sp_wide)

        # 9) Regression for > 350-bit (360-bit) arbitrary-precision fallback without 320-bit truncation:
        mod360 = 1 << 360
        u360 = (((3 << 358) - 1) * pow(9, -1, mod360)) % mod360
        if (u360 & 1) == 0:
            u360 += mod360
        z360 = 4 * u360 - 1
        _, _, sc360, rc360 = run_two_vertex_hensel_bands(
            z360 - 100, z360 + 1000, (9 * (z360 + 1)) // 8 + 100,
            z360 - 50, z360 + 1000, 1, 0,
            [(2, z360 - 8, z360 + 8, u360 - 2, u360 + 2)],
            use_c=True,
        )
        self.assertEqual(rc360, 0)
        self.assertIn(z360, sc360)

        # 10) Direct r = 0 jump over B2 in bridge_mode = 0 raises AssertionError:
        for use_c_flag in (True, False):
            with self.assertRaises(AssertionError):
                run_two_vertex_hensel_bands(
                    10, 50, 100, 20, 50, 1, 0, [(2, 11, 200, 3, 51)], use_c=use_c_flag
                )

        # 11) ValueError checks:
        with self.assertRaises(ValueError):
            run_two_vertex_hensel_bands(10, 50, 100, 20, 50, -1, 0, [])
        with self.assertRaises(ValueError):
            run_two_vertex_hensel_bands(10, 50, 100, 20, 50, 16, 0, [])
        with self.assertRaises(ValueError):
            run_two_vertex_hensel_bands(10, 50, 100, 20, 50, 1, 0, [], max_budget=-1)
        with self.assertRaises(ValueError):
            run_two_vertex_hensel_bands(10, -1, 100, 20, 50, 1, 0, [])
        with self.assertRaises(ValueError):
            verify_prime_denom_rigidity_and_two_vertex_frontier(N0=4)
        with self.assertRaises(ValueError):
            verify_prime_denom_rigidity_and_two_vertex_frontier(max_r_upper_cert=0)
        with self.assertRaises(ValueError):
            verify_prime_denom_rigidity_and_two_vertex_frontier(max_budget_per_m=10)

        # 12) Verify Lean 4 formalization of Theorems 29-31 in CollatzFormal:
        from collatz_analysis.formal_proofs import read_all_collatz_lean_sources

        lean_src = read_all_collatz_lean_sources()
        for expected_thm in (
            "general_affine_converse_universal",
            "general_affine_backward_merger_step",
            "minimal_counterexample_general_backward_merger_exclusion",
            "minimal_counterexample_mod12_in_3_or_7",
            "minimal_counterexample_mod9_ne_4",
            "minimal_counterexample_mod36_in_5_classes",
            "garden_of_eden_div3_unmergeable",
            "initial_bit_exhaustion_iter_lt_pow3",
            "bounded_minimal_counterexample_implies_nontrivial_cycle",
            "syracuseTree_overlap_witnesses",
            "syracuseForestRoot_iff_not_child",
            "syracuseForestVal_injective",
            "backward_carry_window_mixing_implies_collatz_standard",
            "multi_root_forest_collision_implies_collatz_standard",
            "collatz_standard_iff_backward_carry_window",
            "collatz_standard_iff_multi_root_forest_collision",
            "collatz_standard_iff_sieved_backward_carry_window",
            "collatz_standard_iff_sieved_forest_collision",
            "cycle_2adic_valuation_lock_replicate_false",
            "weight2_carry_mod23_never_zero",
            "weight3_mod23_and_neg17_mod139_falsification_witnesses",
            "two_vertex_ordered_minimum_budget_split",
            "s_low_top_strip_upper_bound",
        ):
            self.assertIn(expected_thm, lean_src)

    def test_theorem_32_two_return_escape_and_mod1296_sieve(self) -> None:
        res = verify_two_return_escape_and_mod1296_sieve()
        self.assertTrue(res["affine_carry_append_verified"])
        self.assertTrue(res["suffix_zero_invariance_verified"])
        self.assertTrue(res["forward_2adic_3adic_fiber_constancy_verified"])
        self.assertTrue(res["two_return_garden_of_eden_escape_verified"])
        self.assertGreater(res["div3_escape_transitions_checked"], 400)
        self.assertTrue(res["suffix_shift_mod81_surjectivity_verified"])
        self.assertTrue(res["noncontractive_L5_b3_falsified"])
        self.assertEqual(res["exhaustive_mod1296_surviving_count"], 131)
        self.assertTrue(res["exact_131_mod1296_match_verified"])
        self.assertTrue(res["class_1275_div3_two_stage_escape_verified"])
        self.assertEqual(res["invertible_mod81_surviving_count"], 17)
        self.assertTrue(res["ramanujan_primitive_orthogonality_verified"])
        self.assertTrue(res["mod1296_sieved_forest_prop_verified"])
        self.assertGreater(res["mod1296_sieved_integers_checked"], 250)
        self.assertTrue(res["m1_q2_19_5_29_5_audit_verified"])
        self.assertTrue(res["m2_z_neg_1_5_17_audit_verified"])
        self.assertTrue(res["m3_5n1_5_13_17_audit_verified"])
        self.assertTrue(res["counter_models_all_three_audited"])

        # Boundary checks on is_surviving_mod1296_class:
        self.assertFalse(is_surviving_mod1296_class(3))
        self.assertTrue(is_surviving_mod1296_class(7))
        self.assertFalse(is_surviving_mod1296_class(10))
        self.assertTrue(is_surviving_mod1296_class(27))
        self.assertFalse(is_surviving_mod1296_class(31))
        self.assertFalse(is_surviving_mod1296_class(91))  # 91 % 81 == 10
        self.assertFalse(is_surviving_mod1296_class(1275))  # 0 mod 3 killed at K=4, L=10, b=7
        self.assertEqual(
            sum(1 for r in range(1296) if is_surviving_mod1296_class(r)),
            131,
        )

        # Error-path checks:
        with self.assertRaises(ValueError):
            verify_two_return_escape_and_mod1296_sieve(max_concat_len=1)
        with self.assertRaises(ValueError):
            verify_two_return_escape_and_mod1296_sieve(max_x1_escape=10)
        with self.assertRaises(ValueError):
            verify_two_return_escape_and_mod1296_sieve(max_n_prop_check=500)

        from collatz_analysis.formal_proofs import read_all_collatz_lean_sources

        lean_src = read_all_collatz_lean_sources()
        for expected_thm in (
            "affineCarry_append",
            "affineCarry_append_replicate_false",
            "two_return_garden_of_eden_escape",
            "two_return_sub_3_2_pin_mod3_eq_1",
            "forward_k_mod3_const_on_2adic_fiber",
            "noncontractive_backward_word_falsification_L5_b3",
            "minimal_counterexample_mod16_in_3_classes",
            "minimal_counterexample_mod81_ne_10",
            "minimal_counterexample_mod1296_ne_1275",
            "survivingMod1296_count_eq_131",
            "minimal_counterexample_mod1296_in_131_classes",
            "collatz_standard_iff_mod1296_sieved_forest_collision",
            "two_return_escape_suffix_congruence_mod81",
        ):
            self.assertIn(expected_thm, lean_src)

    def test_theorem_33_unconditional_m99_hensel_elimination(self) -> None:
        res = prove_m99_unconditional_hensel_frontier(
            N0=1 << 71,
            max_m_full=99,
            max_workers=1,
            pairs_override=[(99, 8), (99, 9)],
        )
        self.assertEqual(res["max_m_proved_unconditionally"], 99)
        self.assertEqual(res["proved_m_range"], (1, 99))
        self.assertEqual(res["q43_denominator"], 205632218873398596256)
        self.assertEqual(res["p43_numerator"], 325919355854421968365)
        self.assertEqual(res["monotone_tail_cutoff_u_by_m"][99], 15)
        self.assertTrue(res["u1_99_dominates_97_and_98_verified"])
        self.assertTrue(res["pyramid_demorgan_identity_verified"])
        self.assertTrue(res["native_c23_accelerated"])
        self.assertTrue(res["live_pyramid_l0_to_l2_verified"])
        self.assertGreater(res["live_pyramid_tree_nodes"], 0)
        self.assertTrue(res["zero_cycle_survivors_verified"])
        self.assertEqual(res["total_cycle_survivors"], 0)
        self.assertGreater(res["lean_97_99_survivor_count"], 0)
        self.assertTrue(res["lean_97_99_theorems_present"])
        self.assertTrue(res["lean_97_99_all_drop_verified"])
        self.assertTrue(res["live_survivors_covered_in_lean"])
        self.assertTrue(res["m1_q2_19_5_29_5_audit_verified"])
        self.assertTrue(res["m2_z_neg_1_5_17_audit_verified"])
        self.assertTrue(res["m3_5n1_13_17_audit_verified"])
        self.assertTrue(res["counter_models_all_three_audited"])

        from collatz_analysis.formal_proofs import read_all_collatz_lean_sources

        lean_src = read_all_collatz_lean_sources()
        for expected_thm in (
            "no_nontrivial_spiral_cycles_1_to_93",
            "no_nontrivial_spiral_cycles_m94_u_ge_2",
            "no_nontrivial_spiral_cycles_m95_u_ge_3",
            "no_nontrivial_spiral_cycles_m96_u_ge_4",
            "all_new_m97_to_99_hensel_survivors_drop_below_2_pow_71",
            "m97_to_99_hensel_survivor_drop_universal",
        ):
            self.assertIn(expected_thm, lean_src)

        # Error-path checks:
        with self.assertRaises(ValueError):
            prove_m99_unconditional_hensel_frontier(N0=1)
        with self.assertRaises(ValueError):
            prove_m99_unconditional_hensel_frontier(max_m_full=96)
        with self.assertRaises(ValueError):
            prove_m99_unconditional_hensel_frontier(max_m_full=100)
        with self.assertRaises(ValueError):
            prove_m99_unconditional_hensel_frontier(max_budget=100)
        with self.assertRaises(ValueError):
            prove_m99_unconditional_hensel_frontier(pairs_override=[(90, 1)])


if __name__ == "__main__":
    unittest.main()
