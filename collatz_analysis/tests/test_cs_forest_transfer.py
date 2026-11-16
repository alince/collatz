"""
Unit tests for `collatz_analysis.cs_forest_transfer` (Track 3: Universal All-Weight
`(Z / 3^w Z)*` Surjectivity, Exact Backward Quotient Compression, Koopman Spectral
Factorization, and 3x3 Counter-Model Gate).
"""

from __future__ import annotations

import unittest
from fractions import Fraction

from collatz_analysis.cs_forest_transfer import (
    DLOG2_MOD81_LEAN_TABLE,
    backward_one_total_steps,
    canonical_suffix_shift,
    collapse_forest_collision_to_core_contraction,
    collatz_compressed_int,
    collatz_iter_int,
    convert_forest_witness_to_core_quotient,
    convert_window_witness_to_core_quotient,
    core_strip_word,
    dlog2_mod_pow3_aux,
    dlog2_shift_mod_pow3,
    encode_convergent_odd_to_first_hit_pair,
    exact_backward_quotient,
    horizon_supercritical_reduce,
    is_core_parity_word,
    is_first_hit_one_pair,
    is_horizon_supercritical_for,
    is_supercritical_core_word,
    is_surviving_mod373248_class,
    koopman_branch0,
    koopman_branch1,
    pow2_totient_quot,
    run_all_track3_forest_transfer_verifications,
    scaled_koopman,
    supercritical_core_reduce,
    trivial_loop_extend_one_pair,
    verify_all_weight_primitive_root_and_exact_division,
    verify_compressed_quotient_equivalences,
    verify_forest_transfer_counter_model_gate,
    verify_koopman_spectral_and_ramanujan_orthogonality,
    verify_wave2_supercritical_collapse_and_archimedean_bottleneck,
    verify_wave3_one_generator_bijection_and_range_equivalence,
)
from collatz_analysis.boost_mechanisms import syracuse_forest_val
from collatz_analysis.parity_2adic import affine_parameters


class TestCSForestTransfer(unittest.TestCase):
    """Comprehensive tests for universal all-weight 3^w-adic surjectivity and quotient compression."""

    def test_pow2_totient_quot_exact_3adic_lifting(self) -> None:
        self.assertEqual(pow2_totient_quot(0), 1)
        self.assertEqual(pow2_totient_quot(1), 7)
        self.assertEqual(pow2_totient_quot(2), 9709)
        for m in range(8):
            km = pow2_totient_quot(m)
            self.assertEqual(km % 3, 1)
            self.assertEqual(1 << (2 * (3**m)), 1 + (3 ** (m + 1)) * km)
        with self.assertRaises(ValueError):
            pow2_totient_quot(-1)

    def test_constructive_hensel_dlog_scales_to_high_weights(self) -> None:
        # Match BoostMechanisms.lean dlog2Mod81Table at w = 4 (m = 3)
        for r in range(81):
            if r % 3 != 0:
                self.assertEqual(dlog2_mod_pow3_aux(3, r), DLOG2_MOD81_LEAN_TABLE[r])

        # Test O(w) Hensel lifting up to w = 25 (3^25 = 847,288,609,443) with zero lookup tables!
        for w in (1, 2, 5, 10, 15, 20, 25):
            m = w - 1
            mod_3w = 3**w
            phi_3w = 2 * (3**m)
            for r in (1, 2, 4, 5, 7, 10**9 + 7, mod_3w - 1, mod_3w - 2):
                if r % 3 == 0:
                    continue
                a = dlog2_mod_pow3_aux(m, r)
                self.assertGreaterEqual(a, 0)
                self.assertLess(a, phi_3w)
                self.assertEqual(pow(2, a, mod_3w), r % mod_3w)

                # Test dlog2_shift_mod_pow3 at high weight
                shift = dlog2_shift_mod_pow3(w, r, 5)
                self.assertGreaterEqual(shift, 0)
                self.assertLess(shift, phi_3w)
                self.assertEqual((pow(2, shift, mod_3w) * r) % mod_3w, 5 % mod_3w)

        with self.assertRaises(ValueError):
            dlog2_mod_pow3_aux(2, 9)
        with self.assertRaises(ValueError):
            dlog2_shift_mod_pow3(0, 1, 1)

    def test_all_weight_primitive_root_and_exact_division_certificate(self) -> None:
        cert = verify_all_weight_primitive_root_and_exact_division(
            max_w_lifting=8,
            max_w_bijection=6,
            max_word_len=6,
            max_odd_seed=150,
        )
        self.assertTrue(cert["exact_pow2_totient_lifting_verified"])
        self.assertTrue(cert["minimal_order_totient_verified"])
        self.assertTrue(cert["constructive_hensel_bijection_verified"])
        self.assertTrue(cert["three_coset_hensel_balance_verified"])
        self.assertTrue(cert["lean_dlog2_mod81_exact_match"])
        self.assertTrue(cert["odd_start_escape_verified"])
        self.assertTrue(cert["universal_exact_positive_division_verified"])
        self.assertTrue(cert["exact_q_shift_recurrence_verified"])
        self.assertTrue(cert["mod3_quotient_cyclicity_verified"])
        self.assertTrue(cert["core_word_reduction_identities_verified"])
        self.assertGreater(cert["divisions_verified"], 2000)

    def test_sign_dichotomy_positive_vs_negative_quotients(self) -> None:
        # Edge case: u = (1, 1, 1, 1) has C(u) = 65 > 16*4 = 64 at x2 = 4,
        # yet canonical_suffix_shift gives a = 25 and exact positive quotient y >= 1!
        u_w4 = (1, 1, 1, 1)
        a_4 = canonical_suffix_shift(u_w4, 4)
        y_pos = exact_backward_quotient(4, u_w4, 0)
        self.assertEqual(a_4, 25)
        self.assertEqual(y_pos, ((1 << 29) * 4 - 65) // 81)
        self.assertGreaterEqual(y_pos, 1)
        self.assertEqual(collatz_iter_int(y_pos, 4 + a_4), 4)

        # Negative x2 in M2 = Z^- (-1, -5, -17) yields exact division with y <= -1!
        for z_neg in (-1, -5, -17):
            a_neg = canonical_suffix_shift(u_w4, z_neg)
            y_neg = exact_backward_quotient(z_neg, u_w4, 0)
            self.assertLessEqual(y_neg, -1)
            self.assertEqual(collatz_iter_int(y_neg, 4 + a_neg), z_neg)
            _, w, c_u = affine_parameters(u_w4)
            self.assertEqual((1 << (4 + a_neg)) * z_neg, (3**w) * y_neg + c_u)

    def test_core_word_predicate_and_compressed_collatz_equivalences(self) -> None:
        self.assertTrue(is_core_parity_word((1,)))
        self.assertTrue(is_core_parity_word((1, 0, 0, 1)))
        self.assertFalse(is_core_parity_word(()))
        self.assertFalse(is_core_parity_word((0, 1)))
        self.assertFalse(is_core_parity_word((1, 0)))

        # Verify canonical witnesses at x_K = 1:
        self.assertEqual(exact_backward_quotient(1, (1,), 0), 1)
        self.assertEqual(exact_backward_quotient(1, (1,), 1), 5)

        # Check 1275 mod 1296 (0 mod 3 start -> T^4(1275) = 2153 -> core word (1,1,1,1,0,1,1,1) gives 1007 < 1275!)
        x4_1275 = collatz_iter_int(1275, 4)
        self.assertEqual(x4_1275, 2153)
        u_core_1275 = (1, 1, 1, 1, 0, 1, 1, 1)
        self.assertTrue(is_core_parity_word(u_core_1275))
        self.assertEqual(canonical_suffix_shift(u_core_1275, x4_1275), 2)
        self.assertEqual(exact_backward_quotient(x4_1275, u_core_1275, 0), 1007)

        cert = verify_compressed_quotient_equivalences(max_n_check=2600, max_core_len=5)
        self.assertTrue(cert["canonical_x1_witnesses_verified"])
        self.assertTrue(cert["core_quotient_contraction_prop_verified"])
        self.assertTrue(cert["core_forest_quotient_collision_prop_verified"])
        self.assertTrue(cert["mersenne_high_glide_stress_verified"])
        self.assertEqual(cert["mersenne_surviving_mod1296_count"], 114)
        self.assertGreaterEqual(cert["sieved_mod1296_integers_checked"], 260)
        self.assertGreater(cert["pre_one_core_contraction_hits"], 150)

    def test_koopman_spectral_factorization_and_ramanujan_orthogonality(self) -> None:
        cert = verify_koopman_spectral_and_ramanujan_orthogonality(
            max_w_charpoly=3,
            max_w_stationary=4,
            max_w_ramanujan=5,
        )
        self.assertTrue(cert["koopman_charpoly_factorization_verified"])
        self.assertEqual(cert["universal_spectral_gap"], Fraction(1, 2))
        self.assertTrue(cert["stationary_zero_on_garden_of_eden_verified"])
        self.assertTrue(cert["pi_1_exact_0_1third_2thirds"])
        self.assertEqual(cert["nonprimitive_stationary_modulus_squared"], Fraction(1, 3))
        self.assertTrue(cert["ramanujan_three_regime_all_xi_verified"])

    def test_mandatory_3x3_counter_model_gate_and_full_suite(self) -> None:
        gate = verify_forest_transfer_counter_model_gate()
        self.assertTrue(gate["m1_q2_escape_and_division_verified"])
        self.assertTrue(gate["m1_q2_integrality_obstruction_verified"])
        self.assertTrue(gate["m1_q2_sign_dichotomy_failure_verified"])
        self.assertTrue(gate["m1_q2_rational_contraction_verified"])
        self.assertTrue(gate["m2_z_neg_3adic_exact_division_holds"])
        self.assertTrue(gate["m2_z_neg_quotient_always_le_neg1"])
        self.assertTrue(gate["m2_z_neg_cycles_in_s_infty"])
        self.assertTrue(gate["m3_5x1_dlog5_bijection_verified"])
        self.assertTrue(gate["m3_5x1_positive_quotients_verified"])
        self.assertTrue(gate["m3_5x1_contraction_into_1_4_blocked"])
        self.assertTrue(gate["m3_5x1_low_trapped_in_1cycle"])
        self.assertTrue(gate["counter_model_gate_passed"])

        suite = run_all_track3_forest_transfer_verifications()
        self.assertTrue(suite["all_track3_mechanisms_verified"])

    def test_pointwise_per_n_witness_converters(self) -> None:
        # 1. Core stripping monotonicity on arbitrary non-core words (with leading & trailing 0s)
        raw_word = (0, 0, 1, 0, 1, 1, 0, 0, 0)
        u_core = core_strip_word(raw_word)
        self.assertEqual(u_core, (1, 0, 1, 1))
        self.assertTrue(is_core_parity_word(u_core))
        for x_val in (1, 2, 4, 5, 7, 13, 41, 2153):
            self.assertLessEqual(
                exact_backward_quotient(x_val, u_core, 0),
                exact_backward_quotient(x_val, raw_word, 0),
            )

        # 2. Window witness converter: weight-0 case (e.g., n = 15, T^7(15) = 10 < 15, v = ())
        self.assertEqual(collatz_iter_int(15, 7), 10)
        k_out0, u_out0 = convert_window_witness_to_core_quotient(15, 7, ())
        self.assertGreaterEqual(k_out0, 1)
        self.assertTrue(is_core_parity_word(u_out0))
        self.assertEqual(
            exact_backward_quotient(collatz_iter_int(15, k_out0), u_out0, 0),
            5,
        )

        # 3. Window witness converter: non-core positive-weight witness with leading & trailing zeros
        # For n = 1275: T^4(1275) = 2153; padded word (0,) + u_core_1275 + (0, 0) has quotient 2014 > 1275,
        # whereas u_core_1275 + (0, 0) has exact shift a = 2, quotient 1007 < 1275!
        padded_1275 = (1, 1, 1, 1, 0, 1, 1, 1, 0, 0)
        k_out1, u_out1 = convert_window_witness_to_core_quotient(1275, 4, padded_1275)
        self.assertEqual(k_out1, 4)
        self.assertEqual(u_out1, (1, 1, 1, 1, 0, 1, 1, 1))
        self.assertTrue(is_core_parity_word(u_out1))
        self.assertEqual(
            exact_backward_quotient(collatz_iter_int(1275, k_out1), u_out1, 0),
            1007,
        )

        # 4. Window witness converter: k_step = 0 edge case on odd n (e.g., n = 31: (4*31 - 1)/3 = 41 > 31,
        # take n = 47 with non-contractive check or n = 75? Let's construct an exact k_step = 0 witness:
        # For n = 19: u = (0, 1, 0) has L=3, w=1, C=2 -> (8*19 - 2)/3 = 50 > 19;
        # For n = 13: u = (1, 0) has L=2, w=1, C=1 -> (4*13 - 1)/3 = 17 > 13;
        # For n = 11: u = (1,) has L=1, w=1, C=1 -> (2*11 - 1)/3 = 7 < 11!)
        k_out_k0, u_out_k0 = convert_window_witness_to_core_quotient(11, 0, (1,))
        self.assertEqual(k_out_k0, 1)
        self.assertTrue(is_core_parity_word(u_out_k0))
        self.assertEqual(
            exact_backward_quotient(collatz_iter_int(11, k_out_k0), u_out_k0, 0),
            7,
        )

        # 5. Forest collision witness converter: weight-0 (K >= 0), k_step = 0, and multi-period q >= 2!
        # (a) Weight-0 forest hit on n = 27: T^58(27) = 5 = syracuseForestVal(5, ()) via u = ()
        # Let's find exact K where T^K(27) == 5:
        k_hit5 = 0
        cur27 = 27
        while cur27 != 5:
            cur27 = collatz_compressed_int(cur27)
            k_hit5 += 1
        kf0, qf0, uf0 = convert_forest_witness_to_core_quotient(27, k_hit5, 5, (), ())
        self.assertGreaterEqual(kf0, 1)
        self.assertTrue(is_core_parity_word(uf0))
        self.assertEqual(
            exact_backward_quotient(collatz_iter_int(27, kf0), uf0, qf0),
            syracuse_forest_val(5, ()),
        )

        # (b) Forest child witness on n = 31 (r = 13 < 31):
        # 31 -> 47 -> ... -> 40 -> 20 -> 10 -> 5, while n = 19 -> 29 -> 44 -> 22 -> 11 -> 17 -> 26 -> 13!
        # Check: T^7(19) == 13, r = 13 < 19, and syracuse_forest_val(13, (False,)) == 17 (`(4 * 13 - 1) / 3 = 17`)!
        self.assertEqual(syracuse_forest_val(13, (False,)), 17)
        self.assertEqual(collatz_iter_int(19, 7), 13)
        kf1, qf1, uf1 = convert_forest_witness_to_core_quotient(
            19, 7, 13, (False,), (1, 0)
        )
        self.assertEqual((kf1, qf1, uf1), (7, 0, (1,)))
        self.assertEqual(
            exact_backward_quotient(collatz_iter_int(19, kf1), uf1, qf1),
            syracuse_forest_val(13, (False,)),
        )

        # Multi-period q = 2 forest witness: 2^5 * 5 - 1 = 159 = 3 * 53, where 53 = syracuse_forest_val(5, (True,))
        self.assertEqual(syracuse_forest_val(5, (True,)), 53)
        kf_q2, qf_q2, uf_q2 = convert_forest_witness_to_core_quotient(
            27, k_hit5, 5, (True,), (1, 0, 0, 0, 0)
        )
        self.assertEqual((kf_q2, qf_q2, uf_q2), (k_hit5, 2, (1,)))
        self.assertEqual(
            exact_backward_quotient(collatz_iter_int(27, kf_q2), uf_q2, qf_q2),
            53,
        )

        # (c) k_step = 0 forest witness: n = 13 (odd >= 7), r = 5 < 13, cs = (True,) -> syracuse_forest_val(5, (True,)) = 13!
        # Wait: check which child of 5 equals 13:
        child_f = syracuse_forest_val(5, (False,))
        child_t = syracuse_forest_val(5, (True,))
        cs_13 = (False,) if child_f == 13 else (True,)
        self.assertEqual(syracuse_forest_val(5, cs_13), 13)
        kf_k0, qf_k0, uf_k0 = convert_forest_witness_to_core_quotient(13, 0, 5, cs_13, ())
        self.assertEqual((kf_k0, qf_k0, uf_k0), (1, 0, (1,)))
        self.assertEqual(
            exact_backward_quotient(collatz_iter_int(13, kf_k0), uf_k0, qf_k0),
            13,
        )

    def test_wave2_supercritical_collapse_and_archimedean_bottleneck(self) -> None:
        cert = verify_wave2_supercritical_collapse_and_archimedean_bottleneck(max_word_len=7)
        self.assertTrue(cert["prefix_step_law_verified"])
        self.assertTrue(cert["supercritical_core_dominance_verified"])
        self.assertTrue(cert["weight2_supercritical_singleton_11"])
        self.assertTrue(cert["horizon_supercritical_reduction_verified"])
        self.assertTrue(cert["m1_rational_cycle_prefixes_eliminated"])
        self.assertTrue(cert["arbitrary_depth_forest_collapse_verified"])
        self.assertTrue(cert["universal_carry_upper_bound_verified"])
        self.assertTrue(cert["log_shift_bottleneck_verified"])
        self.assertTrue(cert["koopman_fiber_annihilation_verified"])

        # Check exact supercritical core word counts at lengths 1..6:
        # L=1: 1 ([1]), L=2: 1 ([1,1]), L=3: 1 ([1,1,1]), L=4: 2 ([1,1,0,1],[1,1,1,1]), L=5: 3 ([1,1,0,1,1],[1,1,1,0,1],[1,1,1,1,1])
        self.assertEqual(cert["supercritical_count_by_len"][1], 1)
        self.assertEqual(cert["supercritical_count_by_len"][2], 1)
        self.assertEqual(cert["supercritical_count_by_len"][3], 1)
        self.assertEqual(cert["supercritical_count_by_len"][4], 2)
        self.assertEqual(cert["supercritical_count_by_len"][5], 3)

        # Direct unit checks on supercritical_core_reduce and horizon_supercritical_reduce
        self.assertEqual(supercritical_core_reduce((1, 0, 0, 1)), (1,))
        self.assertEqual(supercritical_core_reduce((1, 1, 0, 0, 1, 1)), (1, 1))
        # (1, 1, 0, 1, 0, 1) has 19/5 prefix (1,1,0,1,0): supercritical at y0=1, but horizon-eliminated at n=7!
        self.assertTrue(is_supercritical_core_word((1, 1, 0, 1, 0, 1)))
        self.assertFalse(is_horizon_supercritical_for(7, (1, 1, 0, 1, 0, 1)))
        self.assertEqual(horizon_supercritical_reduce(7, (1, 1, 0, 1, 0, 1)), (1,))

        # Direct check of T3.8 depth collapse on huge depth-5 Syracuse forest node above r = 5 < n = 27
        cs_deep = (True, True, False, True, True)
        z_deep = syracuse_forest_val(5, cs_deep)
        self.assertGreater(z_deep, 10000)
        # Find K where T^K(27) == 5, and step z_deep to 5:
        k_27 = 0
        cur_27 = 27
        while cur_27 != 5:
            cur_27 = collatz_compressed_int(cur_27)
            k_27 += 1
        cur_z = z_deep
        bits_z = []
        while cur_z != 5:
            bits_z.append(cur_z & 1)
            cur_z = collatz_compressed_int(cur_z)
        k_coll, u_coll = collapse_forest_collision_to_core_contraction(
            27, k_27, 5, cs_deep, bits_z
        )
        self.assertTrue(is_core_parity_word(u_coll))
        self.assertLessEqual(
            exact_backward_quotient(collatz_iter_int(27, k_coll), u_coll, 0),
            5,
        )

        # Direct check of Koopman w=1 constancy: koopman_branch1(1, b) == 2 for all b
        for b in range(9):
            self.assertEqual(koopman_branch1(1, b), 2)
        self.assertEqual(scaled_koopman(1, [10, 20, 30], 0), 10 + 30)

    def test_wave3_one_generator_bijection_and_range_equivalence(self) -> None:
        cert = verify_wave3_one_generator_bijection_and_range_equivalence(
            max_word_len=7, max_odd_bijection=5001, max_sieved_n=10000
        )
        self.assertTrue(cert["t313_generator_sound_verified"])
        self.assertTrue(cert["t313_singleton_closed_form_verified"])
        self.assertTrue(cert["t313_loop_degeneracy_verified"])
        self.assertTrue(cert["t314_grid_injective_verified"])
        self.assertTrue(cert["t314_roundtrip_bijection_verified"])
        self.assertEqual(cert["odd_integers_bijected_count"], 2500)
        self.assertTrue(cert["mod373248_sieve_factored_count_verified"])
        self.assertTrue(cert["t315_mod373248_range_verified"])
        self.assertGreater(cert["sieved_mod373248_integers_checked"], 250)
        self.assertGreaterEqual(cert["min_sieved_first_hit_weight_observed"], 3)
        self.assertTrue(cert["t316_sharpened_prefix_weight_verified"])
        self.assertTrue(cert["t316_weight_le2_exclusion_verified"])
        self.assertTrue(cert["wave3_counter_model_gate_passed"])

        # Explicit T3.13b closed-form checks: (4^(q+1) - 1) // 3 = 1, 5, 21, 85, 341
        self.assertEqual(
            [exact_backward_quotient(1, (1,), q) for q in range(5)],
            [1, 5, 21, 85, 341],
        )

        # Explicit T3.14 boundary checks on IsFirstHitOnePair:
        # (a) k = 0 check rejects (u = (1,), q = 0) where y = 1!
        self.assertEqual(exact_backward_quotient(1, (1,), 0), 1)
        self.assertEqual(backward_one_total_steps((1,), 0), 2)
        self.assertFalse(is_first_hit_one_pair((1,), 0))
        # (b) (u = (1,), q = 1) gives y = 5 > 1, first-hit in 4 steps -> accepted!
        self.assertTrue(is_first_hit_one_pair((1,), 1))
        # (c) 1 <= k < L check rejects loop-extended (1, 0, 0, 0, 1), q = 0 where y = 5 > 1 hits 1 at k = 4 < 6!
        u_loop_5 = trivial_loop_extend_one_pair((1,), 1)
        self.assertEqual(u_loop_5, (1, 0, 0, 0, 1))
        self.assertEqual(exact_backward_quotient(1, u_loop_5, 0), 5)
        self.assertEqual(backward_one_total_steps(u_loop_5, 0), 6)
        self.assertFalse(is_first_hit_one_pair(u_loop_5, 0))

        # Explicit T3.15/T3.16 check on high-glide seed n = 27 (smallest Mod-373248 survivor):
        self.assertTrue(is_surviving_mod373248_class(27))
        u27, q27 = encode_convergent_odd_to_first_hit_pair(27)
        self.assertTrue(is_first_hit_one_pair(u27, q27))
        self.assertEqual(exact_backward_quotient(1, u27, q27), 27)
        self.assertEqual(u27[:2], (1, 1))
        self.assertEqual(sum(u27), 41)

    def test_input_validation_errors(self) -> None:
        with self.assertRaises(ValueError):
            canonical_suffix_shift((0, 0), 5)
        with self.assertRaises(ValueError):
            exact_backward_quotient(5, (0,), 0)
        with self.assertRaises(ValueError):
            exact_backward_quotient(5, (1,), -1)
        with self.assertRaises(ValueError):
            backward_one_total_steps((1, 0), 0)
        with self.assertRaises(ValueError):
            encode_convergent_odd_to_first_hit_pair(1)
        with self.assertRaises(ValueError):
            encode_convergent_odd_to_first_hit_pair(6)


if __name__ == "__main__":
    unittest.main()
