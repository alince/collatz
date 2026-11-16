"""Unit tests for Track 1 (`cs_lp_cycles.py`): Exact LP/Farkas & Universal Cycle Reductions."""

from __future__ import annotations

from fractions import Fraction
from itertools import product
import unittest

from collatz_analysis.cs_lp_cycles import (
    MOD12_SURVIVING_CYCLE_MAX_ODD_CLASSES,
    MOD16_SURVIVING_CYCLE_MIN_CLASSES,
    MOD24_DETERMINANT_CLASSES,
    MOD24_ONE_BLOCK_Q0_CLASSES,
    MOD32_SURVIVING_CYCLE_MIN_CLASSES,
    MOD48_SURVIVING_CYCLE_MIN_CLASSES,
    MOD96_ONE_BLOCK_X0_CLASSES,
    MOD96_SURVIVING_CYCLE_MIN_CLASSES,
    DirectedEdge,
    affine_carry,
    bezout_coprime_pow2_pow3,
    brox_odd_carry,
    build_archimedean_macro_spiral_graph,
    build_modular_spiral_graph,
    check_subexponential_cubic_gap,
    collatz_step_int,
    construct_modular_pseudo_cycle_witness,
    construct_sturmian_rational_cycle,
    decompose_spiral_blocks,
    evaluate_cycle_barriers_on_word,
    exact_karp_min_mean_cycle,
    generalized_thm19_1_reciprocal_drift,
    is_primitive_two_block_brox_witness,
    is_sharpened_brox_cycle_witness,
    is_wave3_sharpened_brox_witness,
    parity_weight,
    parity_word_from_spiral_blocks,
    rational_cycle_from_parity_word,
    reconstruct_rational_pseudo_cycle,
    rotate_left,
    run_3x3_countermodel_gate,
    shifted_reciprocal_step_slack,
    step_contraction_lower_bound,
    two_block_brox_carries,
    verify_2adic_lte_pow3_sub_one,
    verify_brox_append_false_identity,
    verify_brox_shift_identity,
    verify_cycle_ratio_sandwich_and_peak_floor,
    verify_farkas_circulation,
    verify_first_block_discreteness_separation,
    verify_hercher_subdouble_merger_separation,
    verify_mod24_determinant_gap,
    verify_multipole_rational_potential_annihilation,
    verify_one_block_cycle_squeeze,
    verify_one_block_gcd_and_mod24_squeeze,
    verify_potential_certificate,
    verify_rational_cycle_amgm_nonpositive,
    verify_two_block_cleared_denom_and_cubic_squeeze,
    verify_two_block_m1_potential_obstruction_witnesses,
)


class TestExactKarpFarkasSolver(unittest.TestCase):
    """Test exact `Fraction` Karp minimum-mean-cycle and primal/dual certificates."""

    def test_multi_scc_positive_zero_and_negative_regimes(self) -> None:
        vertices = ["a", "b", "c", "d"]

        # Regime 1: strictly positive minimum mean cost (mu* = 1/3).
        edges_pos = [
            DirectedEdge("a", "b", Fraction(1, 2), (1,)),
            DirectedEdge("b", "a", Fraction(1, 6), (2,)),  # mean = (1/2 + 1/6)/2 = 1/3
            DirectedEdge("c", "d", Fraction(3, 1), (3,)),
            DirectedEdge("d", "c", Fraction(-1, 1), (4,)),  # mean = 1 > 1/3
        ]
        res_pos = exact_karp_min_mean_cycle(vertices, edges_pos)
        self.assertTrue(res_pos.has_universal_potential)
        self.assertEqual(res_pos.min_mean_cost, Fraction(1, 3))
        assert res_pos.potentials is not None
        self.assertTrue(
            verify_potential_certificate(
                edges_pos, res_pos.potentials, res_pos.min_mean_cost
            )
        )

        # Regime 2: exact zero minimum mean cost (mu* = 0 -> Farkas obstruction!).
        edges_zero = [
            DirectedEdge("a", "b", Fraction(2, 5), (1,)),
            DirectedEdge("b", "a", Fraction(-2, 5), (2,)),  # mean = 0
            DirectedEdge("c", "d", Fraction(5, 2), (3,)),
            DirectedEdge("d", "c", Fraction(1, 2), (4,)),  # mean = 3/2
        ]
        res_zero = exact_karp_min_mean_cycle(vertices, edges_zero)
        self.assertFalse(res_zero.has_universal_potential)
        self.assertEqual(res_zero.min_mean_cost, Fraction(0))
        assert res_zero.farkas_circulation is not None
        assert res_zero.farkas_cycle is not None
        self.assertTrue(
            verify_farkas_circulation(
                vertices, edges_zero, res_zero.farkas_circulation, res_zero.farkas_cycle
            )
        )

        # Regime 3: strictly negative minimum mean cost (mu* = -1/4) + self-loop check.
        edges_neg = [
            DirectedEdge("a", "b", Fraction(1, 2), (1,)),
            DirectedEdge("b", "a", Fraction(1, 2), (2,)),
            DirectedEdge("c", "c", Fraction(-1, 4), (3,)),
        ]
        res_neg = exact_karp_min_mean_cycle(vertices, edges_neg)
        self.assertFalse(res_neg.has_universal_potential)
        self.assertEqual(res_neg.min_mean_cost, Fraction(-1, 4))
        assert res_neg.farkas_circulation is not None
        assert res_neg.farkas_cycle is not None
        self.assertTrue(
            verify_farkas_circulation(
                vertices, edges_neg, res_neg.farkas_circulation, res_neg.farkas_cycle
            )
        )

    def test_dag_gives_universal_potential(self) -> None:
        vertices = [0, 1, 2]
        edges = [
            DirectedEdge(0, 1, Fraction(-5, 3), (1, 1)),
            DirectedEdge(1, 2, Fraction(-7, 2), (2, 1)),
        ]
        res = exact_karp_min_mean_cycle(vertices, edges)
        self.assertTrue(res.has_universal_potential)
        assert res.potentials is not None
        self.assertTrue(
            verify_potential_certificate(edges, res.potentials, res.min_mean_cost)
        )

    def test_contracting_spiral_subgraph_synthesizes_universal_potential(self) -> None:
        # On steps with l >= k and floor n0 = 4, 2^(k+l) >= 4^k > 3^k + (3^k - 2^k)/4,
        # OR even with mixed non-contracting single steps that cannot close a cycle
        # (e.g., k=3, l=1 requires r == 7 mod 16 -> r_next, restricted to {k=1, l>=1} at n0=2).
        allowed = [(1, 1), (1, 2), (2, 2), (3, 3)]
        for mode in ("step_contraction", "shifted_reciprocal"):
            verts, edges = build_modular_spiral_graph(
                A=3, B=2, allowed_steps=allowed, n0_floor=4, cost_mode=mode
            )
            self.assertGreater(len(edges), 0)
            res = exact_karp_min_mean_cycle(verts, edges)
            self.assertTrue(res.has_universal_potential)
            self.assertGreater(res.min_mean_cost, Fraction(0))
            assert res.potentials is not None
            self.assertTrue(
                verify_potential_certificate(edges, res.potentials, res.min_mean_cost)
            )

    def test_unconstrained_modular_spiral_surfaces_m2_farkas_witness(self) -> None:
        # Allowing (k=2, l=1) without global 2^K > 3^W produces mu* < 0 and surfaces
        # a negative-determinant (M2 = Z^-) pseudo-cycle witness (such as -5: k=2, l=1).
        verts, edges = build_modular_spiral_graph(
            A=3, B=1, allowed_steps=[(1, 1), (2, 1)], n0_floor=7
        )
        res = exact_karp_min_mean_cycle(verts, edges)
        self.assertFalse(res.has_universal_potential)
        self.assertLessEqual(res.min_mean_cost, Fraction(0))
        assert res.farkas_circulation is not None
        assert res.farkas_cycle is not None
        self.assertTrue(
            verify_farkas_circulation(
                verts, edges, res.farkas_circulation, res.farkas_cycle
            )
        )
        recon = reconstruct_rational_pseudo_cycle(res.farkas_cycle, A=3, B=1)
        self.assertTrue(recon["modular_projection_matches"])
        self.assertLess(int(recon["determinant"]), 0)

    def test_archimedean_macro_spiral_surfaces_m1_positive_rational_witnesses(self) -> None:
        # Enforce 2^K > 3^W (eliminating ALL M2 = Z^- cycles!) AND l_i = 1 (Hercher filter!).
        # 1. At max_macro_len=2, n0_floor=4: surfaces 29/5 <-> 23/5 (K=5, W=3, D=5)!
        verts2, edges2 = build_archimedean_macro_spiral_graph(
            A=3, B=1, single_steps=[(1, 1), (2, 1)], max_macro_len=2, n0_floor=4
        )
        res2 = exact_karp_min_mean_cycle(verts2, edges2)
        self.assertFalse(res2.has_universal_potential)
        assert res2.farkas_cycle is not None
        assert res2.farkas_circulation is not None
        self.assertTrue(
            verify_farkas_circulation(
                verts2, edges2, res2.farkas_circulation, res2.farkas_cycle
            )
        )
        recon2 = reconstruct_rational_pseudo_cycle(res2.farkas_cycle, A=3, B=1)
        self.assertTrue(recon2["is_positive_rational_cycle"])
        self.assertFalse(recon2["is_integer_cycle"])
        self.assertTrue(recon2["modular_projection_matches"])
        self.assertGreater(int(recon2["determinant"]), 0)
        self.assertGreaterEqual(recon2["min_value"], Fraction(4))

        # 2. Raise floor to n0_floor=24 (killing 19/5 and 29/5!) with max_macro_len=3:
        # Karp STILL returns mu* <= 0 by discovering high-floor M1 witness 319/13 > 24!
        verts3, edges3 = build_archimedean_macro_spiral_graph(
            A=4, B=1, single_steps=[(1, 1), (2, 1)], max_macro_len=3, n0_floor=24
        )
        res3 = exact_karp_min_mean_cycle(verts3, edges3)
        self.assertFalse(res3.has_universal_potential)
        assert res3.farkas_cycle is not None
        assert res3.farkas_circulation is not None
        self.assertTrue(
            verify_farkas_circulation(
                verts3, edges3, res3.farkas_circulation, res3.farkas_cycle
            )
        )
        recon3 = reconstruct_rational_pseudo_cycle(res3.farkas_cycle, A=4, B=1)
        self.assertTrue(recon3["is_positive_rational_cycle"])
        self.assertFalse(recon3["is_integer_cycle"])
        self.assertTrue(recon3["modular_projection_matches"])
        self.assertGreater(recon3["min_value"], Fraction(24))


class TestBoundedModulusObstructionTheoremT4(unittest.TestCase):
    """Test Theorem T4 constructive Bezout lifting and `(2^A * 3^B)` obstruction."""

    def test_constructive_bezout_coprime_pow2_pow3(self) -> None:
        for d in (1, 5, 7, 11, 13, 17, 19, 23, 25, 47, 139):
            for A in range(6):
                for B in range(4):
                    u_val, v_val = bezout_coprime_pow2_pow3(d, A, B)
                    modulus = (1 << A) * (3**B)
                    self.assertEqual(d * u_val + modulus * v_val, 1)

    def test_universal_modular_pseudo_cycle_witnesses_across_moduli(self) -> None:
        witness_words = [
            [True, True, True, False, False],  # 19/5 (D = 5)
            [True, False, True, True, False],  # 29/5 (D = 5)
            [True, True, False, True, True, False, True, False],  # 319/13 > 24 (D = 13)
            construct_sturmian_rational_cycle(27, 17),  # Sturmian high-floor (K=27, W=17)
        ]
        for word in witness_words:
            for A in range(5):
                for B in range(3):
                    cert = construct_modular_pseudo_cycle_witness(word, A, B)
                    self.assertTrue(cert["homogeneous_steps_ok"])
                    self.assertTrue(cert["modular_steps_ok"])
                    self.assertTrue(cert["parity_ok"])
                    self.assertTrue(cert["nondiv3_ok"])
                    self.assertTrue(cert["telescoping_sum_zero"])

        # Specifically check 319/13 mod 48 (A=4, B=1): r_0 == 43 in surviving mod-48 set!
        cert_319 = construct_modular_pseudo_cycle_witness(witness_words[2], A=4, B=1)
        residues_48 = cert_319["residues"]
        assert isinstance(residues_48, list)
        self.assertEqual(residues_48[0], 43)
        self.assertIn(residues_48[0], MOD48_SURVIVING_CYCLE_MIN_CLASSES)
        self.assertGreater(cert_319["x_min"], Fraction(24))

    def test_multipole_rational_potential_farkas_annihilation(self) -> None:
        poles = [Fraction(0), Fraction(1), Fraction(2), Fraction(5, 2), Fraction(7)]
        weights = [
            Fraction(3, 1),
            Fraction(-11, 4),
            Fraction(5, 7),
            Fraction(-2, 3),
            Fraction(13, 9),
        ]
        for word in (
            [True, True, True, False, False],
            [True, False, True, True, False],
            [True, True, False, True, True, False, True, False],
        ):
            orbit = rational_cycle_from_parity_word(word, q=3)
            self.assertTrue(verify_rational_cycle_amgm_nonpositive(orbit))
            for A in range(1, 5):
                for B in range(1, 3):
                    self.assertTrue(
                        verify_multipole_rational_potential_annihilation(
                            word, A, B, poles, weights
                        )
                    )

    def test_generalized_thm19_1_step_drift_matches_exact_orbit(self) -> None:
        word = [True, False, True, True, False]  # 29/5 <-> 23/5
        blocks = decompose_spiral_blocks(word)
        self.assertEqual(blocks, [(1, 1), (2, 1)])
        self.assertEqual(parity_word_from_spiral_blocks(blocks), word)
        d0 = generalized_thm19_1_reciprocal_drift(Fraction(29, 5), 1, 1, Fraction(0))
        d1 = generalized_thm19_1_reciprocal_drift(Fraction(23, 5), 2, 1, Fraction(0))
        self.assertEqual(d0 + d1, Fraction(0))
        # Also verify step_contraction and shifted_reciprocal bounds hold on exact step!
        self.assertLessEqual(
            step_contraction_lower_bound(1, 1, 4),
            1 - Fraction(23, 5) / Fraction(29, 5),
        )
        self.assertLessEqual(
            shifted_reciprocal_step_slack(2, 1, 4),
            1 - (Fraction(29, 5) + 1) / (Fraction(23, 5) + 1),
        )


class TestUniversalCycleReductionsAnd3x3Gate(unittest.TestCase):
    """Test Theorems T1, T2, T3a, T3b and the mandatory 3x3 Counter-Model Gate."""

    def test_theorem_t1_ratio_sandwich_and_peak_floor(self) -> None:
        # Trivial {1, 2} cycle achieves tight equality on all three bounds!
        triv_word = [True, False]
        triv_orb = rational_cycle_from_parity_word(triv_word, q=3)
        self.assertEqual(triv_orb, [Fraction(1), Fraction(2)])
        t1_triv = verify_cycle_ratio_sandwich_and_peak_floor(triv_word, triv_orb)
        self.assertTrue(all(t1_triv.values()))

        # Positive rational cycles satisfy T1 with strict m_odd < M_odd when W >= 2 & multi-odd.
        for word in (
            [True, True, True, False, False],
            [True, False, True, True, False],
            [True, True, False, True, True, False, True, False],
            construct_sturmian_rational_cycle(27, 17),
        ):
            orb = rational_cycle_from_parity_word(word, q=3)
            t1_res = verify_cycle_ratio_sandwich_and_peak_floor(word, orb)
            self.assertTrue(all(t1_res.values()))
            odd_vals = [orb[i] for i, b in enumerate(word) if b]
            self.assertLess(min(odd_vals), max(odd_vals))

    def test_theorem_t2_cycle_max_odd_mod12_on_trivial_and_rational_cycles(self) -> None:
        # On trivial {1, 2}, M_odd = 1, 1 % 12 == 1 in {1, 5}.
        self.assertIn(1 % 12, MOD12_SURVIVING_CYCLE_MAX_ODD_CLASSES)
        # On 29/5 (D=5) and 319/13 (D=13), check 12-adic residue of M_odd!
        for word in (
            [True, False, True, True, False],
            [True, True, False, True, True, False, True, False],
        ):
            orb = rational_cycle_from_parity_word(word, q=3)
            odd_vals = [orb[i] for i, b in enumerate(word) if b]
            m_max = max(odd_vals)
            u12, _ = bezout_coprime_pow2_pow3(m_max.denominator, A=2, B=1)
            r_max_12 = (m_max.numerator * u12) % 12
            self.assertIn(r_max_12, MOD12_SURVIVING_CYCLE_MAX_ODD_CLASSES)

    def test_theorem_t3b_brox_odd_carry_identity_exhaustive(self) -> None:
        for w1 in range(6):
            for length in range(7):
                for bits in product([False, True], repeat=length):
                    self.assertTrue(verify_brox_shift_identity(w1, bits))

        # Check closed values on canonical witnesses:
        # 29/5: w1=1, rest=[T, T, F] -> H = 17
        self.assertEqual(brox_odd_carry([True, True, False]), 17)
        # 23/5: w1=2, rest=[T, F] -> H = 7
        self.assertEqual(brox_odd_carry([True, False]), 7)
        # 319/13: w1=2, rest=[T, T, F, T, F] -> H = 83
        self.assertEqual(brox_odd_carry([True, True, False, True, False]), 83)
        # -17 (M2): w1=4, rest=[T, T, T, F, F, F] -> H = 139
        self.assertEqual(
            brox_odd_carry([True, True, True, False, False, False]), 139
        )

    def test_exhaustive_iff_equivalence_up_to_length_10(self) -> None:
        # Exhaustively verify across all non-empty parity words of length 1..10:
        # 1. Every positive integer 3x+1 cycle word is a repetition of [True, False]
        #    or [False, True] (x in {1, 2}), and
        # 2. `certified_nontrivial_3x1_witness` is False on 100% of them!
        for k_len in range(1, 11):
            for bits in product([False, True], repeat=k_len):
                w = parity_weight(bits)
                if w == 0:
                    continue
                det = (1 << k_len) - (3**w)
                if det == 0:
                    continue
                c_val = affine_carry(bits, q=3)
                if det > 0 and (c_val % det == 0):
                    x0 = c_val // det
                    self.assertIn(x0, (1, 2))
                res = evaluate_cycle_barriers_on_word(bits, q=3)
                self.assertFalse(res["certified_nontrivial_3x1_witness"])

    def test_mandatory_3x3_countermodel_gate(self) -> None:
        gate = run_3x3_countermodel_gate()

        # Every single counter-model and trivial witness MUST be rejected by our
        # certified non-trivial (Z^+, 3x+1) equivalence predicate!
        for name, report in gate.items():
            self.assertFalse(
                report["certified_nontrivial_3x1_witness"],
                msg=f"Counter-model {name} was not separated!",
            )

        # Verify exact barrier mechanism per counter-model family:
        # M1 (Q_(2)^+): satisfies archimedean positivity & nondiv3, FAILS Z-integrality
        # (and 19/5, 29/5 ALSO fail the (21, 22) mod-16 band!).
        for m1_key in ("M1_19_over_5", "M1_29_over_5", "M1_319_over_13_high_floor"):
            self.assertTrue(gate[m1_key]["archimedean_positivity_3x1"])
            self.assertTrue(gate[m1_key]["nondiv3_all_vertices"])
            self.assertFalse(gate[m1_key]["z_integrality_3x1"])
        self.assertFalse(gate["M1_19_over_5"]["band_21_22"])
        self.assertFalse(gate["M1_29_over_5"]["band_21_22"])
        self.assertTrue(gate["M1_319_over_13_high_floor"]["band_21_22"])

        # M2 (Z^-: -1, -5, -17): FAILS archimedean positivity (3^W < 2^K and x > 0) AND (21, 22) band.
        for m2_key in ("M2_neg_1", "M2_neg_5", "M2_neg_17"):
            self.assertFalse(gate[m2_key]["archimedean_positivity_3x1"])
            self.assertFalse(gate[m2_key]["band_21_22"])

        # M3 (5x+1 on Z^+: 1, 13, 17): FAILS 2^K <= 4^W, FAILS x % 3 != 0 (all visit multiples of 3!),
        # and FAILS (21, 22) band!
        for m3_key in ("M3_5x1_1", "M3_5x1_13", "M3_5x1_17"):
            self.assertFalse(gate[m3_key]["pow4_upper_bound"])
            self.assertFalse(gate[m3_key]["nondiv3_all_vertices"])
            self.assertFalse(gate[m3_key]["band_21_22"])

        # Trivial {1, 2} cycle of (Z^+, 3x+1): passes Z-integrality & pow4_upper_bound,
        # separated as trivial by mod-48 minimum sieve AND (21, 22) band!
        self.assertTrue(gate["Zpos_3x1_trivial_1"]["z_integrality_3x1"])
        self.assertTrue(gate["Zpos_3x1_trivial_1"]["pow4_upper_bound"])
        self.assertFalse(gate["Zpos_3x1_trivial_1"]["mod48_min_sieve"])
        self.assertFalse(gate["Zpos_3x1_trivial_1"]["band_21_22"])

    def test_rotation_invariance_of_carry_divisibility(self) -> None:
        # Verify cyclic shift carry divisibility equivalence across shifts.
        word = [True, True, False, True, True, False, True, False]
        det = (1 << len(word)) - (3 ** parity_weight(word))
        self.assertEqual(det, 13)
        for j in range(len(word)):
            rot = rotate_left(word, j)
            self.assertNotEqual(affine_carry(rot, q=3) % det, 0)


class TestWave2StructuralReductionsT5ToT8(unittest.TestCase):
    """Test Wave 2 universal structural reductions T5--T8 (`[]` custom axioms)."""

    def test_crt_6_class_mod48_and_8_class_mod96_refinement(self) -> None:
        # Verify exact CRT correspondence:
        # 1. r % 16 in {7,11,15} & r % 3 != 0 <-> 6 classes mod 48.
        crt_48 = frozenset(
            r
            for r in range(48)
            if (r % 16 in MOD16_SURVIVING_CYCLE_MIN_CLASSES) and (r % 3 != 0)
        )
        self.assertEqual(crt_48, MOD48_SURVIVING_CYCLE_MIN_CLASSES)
        self.assertEqual(len(MOD48_SURVIVING_CYCLE_MIN_CLASSES), 6)

        # 2. Forward k=5 descent on 32*q + 11 -> 27*q + 10 and 32*q + 23 -> 27*q + 20,
        #    leaving {7, 15, 27, 31} mod 32 and 8 classes mod 96!
        for q in range(30):
            x11 = 32 * q + 11
            x23 = 32 * q + 23
            for _ in range(5):
                x11 = collatz_step_int(x11)
                x23 = collatz_step_int(x23)
            self.assertEqual(x11, 27 * q + 10)
            self.assertEqual(x23, 27 * q + 20)

        crt_96 = frozenset(
            r
            for r in range(96)
            if (r % 32 in MOD32_SURVIVING_CYCLE_MIN_CLASSES) and (r % 3 != 0)
        )
        self.assertEqual(crt_96, MOD96_SURVIVING_CYCLE_MIN_CLASSES)
        self.assertEqual(len(MOD96_SURVIVING_CYCLE_MIN_CLASSES), 8)

        # 19/5 (23 mod 32) and 23/5 (11 mod 32) are killed mod 32, while 319/13 == 91 mod 96 survives!
        u5_32, _ = bezout_coprime_pow2_pow3(5, A=5, B=0)
        self.assertEqual((19 * u5_32) % 32, 23)
        self.assertEqual((23 * u5_32) % 32, 11)
        u13_96, _ = bezout_coprime_pow2_pow3(13, A=5, B=1)
        self.assertEqual((319 * u13_96) % 96, 91)
        self.assertIn(91, MOD96_SURVIVING_CYCLE_MIN_CLASSES)

    def test_theorem_t5_mod24_determinant_gap(self) -> None:
        seen_classes: set[int] = set()
        for K in range(3, 60):
            for W in range(1, K):
                if (3**W) < (1 << K):
                    res = verify_mod24_determinant_gap(K, W)
                    self.assertTrue(res["in_4_classes"])
                    self.assertTrue(res["ge_5"])
                    seen_classes.add(int(res["mod24"]))
        # All 4 residue classes {5, 7, 13, 23} mod 24 are realized!
        self.assertEqual(seen_classes, set(MOD24_DETERMINANT_CLASSES))

    def test_theorem_t6_2adic_lte_and_one_block_mersenne_elimination(self) -> None:
        # Exhaustively verify 2^a | (3^w - 1) => 2^a <= 4 * w across w = 1..200.
        for w in range(1, 201):
            self.assertTrue(verify_2adic_lte_pow3_sub_one(w))

        # Verify 1-block cycle binary prefix squeeze & q0 = 1 impossibility across w1=2..80, c=0..80.
        for w1 in range(2, 81):
            for c in range(0, 81):
                res = verify_one_block_cycle_squeeze(w1, c)
                self.assertTrue(res["brox_formula_ok"])
                self.assertTrue(res["q0_eq_1_impossible"])
                self.assertTrue(res["binary_prefix_ok"])

    def test_theorem_t7_brox_append_false_and_first_block_discreteness(self) -> None:
        for length in range(8):
            for init in product([False, True], repeat=length):
                self.assertTrue(verify_brox_append_false_identity(init))

        # Verify M1 = Q_(2)^+ 2-block contracting witness 1^3 0^2 1^5 0^3 (D = 1631)
        # violates Z^+ integer-discreteness dichotomy because 0 < x1 - x0 = 808/1631 < 1!
        sep = verify_first_block_discreteness_separation()
        self.assertTrue(sep["gap_strictly_between_0_and_1"])
        self.assertTrue(sep["first_block_contracts_det"])
        self.assertTrue(sep["violates_z_discreteness_dichotomy"])
        self.assertEqual(sep["x0_min"], Fraction(10561, 1631))
        self.assertEqual(sep["x1_next_spiral"], Fraction(11369, 1631))
        self.assertEqual(sep["gap"], Fraction(808, 1631))

    def test_theorem_t8_sharpened_brox_witness_sweep(self) -> None:
        # Verify IsSharpenedBroxCycleWitness is False across all candidate (w1, init, q0)
        # in the boundary sweep K <= 12.
        for w1 in range(2, 9):
            max_init = max(0, 10 - w1)
            for init_len in range(max_init + 1):
                k_len = w1 + 2 + init_len
                if k_len < 8:
                    continue
                for init in product([False, True], repeat=init_len):
                    w = w1 + parity_weight(init)
                    if w < 5:
                        continue
                    det = (1 << k_len) - (3**w)
                    if det <= 0:
                        continue
                    rhs = brox_odd_carry(init) + (1 << (init_len + 1))
                    if rhs % det == 0:
                        q0 = rhs // det
                        self.assertFalse(
                            is_sharpened_brox_cycle_witness(w1, init, q0)
                        )


class TestWave3OneBlockGcdAndTwoBlockReductionT9ToT11(unittest.TestCase):
    """Test Wave 3 1-block GCD/mod-24 squeeze, 2-block reduction, and master core (T9--T11)."""

    def test_theorem_t9_one_block_gcd_lock_pow3_elimination_and_mod24_squeeze(
        self,
    ) -> None:
        # 1. Verify CRT mod-24 survival {3, 9, 17, 19} and mod-96 {31, 95} on 1-block cycles!
        crt_q0_24 = frozenset(
            r
            for r in range(1, 24, 2)
            if any(
                ((r * (3**w_par) - 1) % 8 == 0)
                and (((r * (2**w_par) - 1) % 3) != 0)
                for w_par in (0, 1)
            )
        )
        self.assertEqual(crt_q0_24, MOD24_ONE_BLOCK_Q0_CLASSES)

        crt_x0_96 = frozenset(
            r for r in range(96) if (r % 32 == 31) and (r % 3 != 0)
        )
        self.assertEqual(crt_x0_96, MOD96_ONE_BLOCK_X0_CLASSES)

        # 2. Verify Theorem T9 across w1 = 2..80 and surrounding a1 values.
        for w1 in range(2, 81):
            a_min = (3**w1).bit_length() - w1
            for a1 in range(max(1, a_min - 2), a_min + 6):
                res = verify_one_block_gcd_and_mod24_squeeze(w1, a1)
                self.assertTrue(res["linear_comb_ok"])
                self.assertTrue(res["pow3_quotient_impossible"])
                self.assertTrue(res["small_w1_impossible"])
                self.assertTrue(res["binary_prefix17_ok"])
                self.assertTrue(res["gcd_and_mod_locks_ok"])
                self.assertFalse(res["divisible_hit"])

        # 3. Verify 3x3 counter-model separation on 1-block cycles:
        # M1 (19/5: w1=3, a1=2), M2 (-5: w1=2, a1=1), M3 (13 under 5x+1: w1=3, a1=4).
        for w1, a1 in ((3, 2), (2, 1), (3, 4)):
            res_cm = verify_one_block_gcd_and_mod24_squeeze(w1, a1)
            self.assertFalse(res_cm["divisible_hit"])

    def test_theorem_t10_two_block_reciprocal_identity_mersenne_and_cubic_squeeze(
        self,
    ) -> None:
        # Exhaustively test all 2-block parameters (w1, a1, w2, a2) with W <= 16, K <= 2*W.
        for w_tot in range(2, 17):
            for k_tot in range(w_tot + 2, 2 * w_tot + 1):
                for w1 in range(1, w_tot):
                    w2 = w_tot - w1
                    for a1 in range(1, k_tot - w_tot):
                        a2 = k_tot - w_tot - a1
                        res = verify_two_block_cleared_denom_and_cubic_squeeze(
                            w1, a1, w2, a2, n0_floor=26
                        )
                        self.assertTrue(res["brox_closed_form_ok"])
                        self.assertTrue(res["reciprocal_identity_ok"])
                        self.assertTrue(res["mersenne_q0_impossible"])
                        self.assertTrue(res["mersenne_q1_impossible"])
                        self.assertTrue(res["cubic_squeeze_ok"])
                        self.assertTrue(res["potential_merger_bound_ok"])

    def test_theorem_t10_m1_potential_obstruction_witnesses_251_and_287_over_13(
        self,
    ) -> None:
        obs = verify_two_block_m1_potential_obstruction_witnesses()
        self.assertEqual(obs["witness_251_x0"], Fraction(251, 13))
        self.assertEqual(obs["witness_251_x1"], Fraction(439, 13))
        self.assertTrue(obs["witness_251_satisfies_q_potential"])
        self.assertTrue(obs["witness_251_separated_by_z_and_23D"])

        self.assertEqual(obs["witness_287_x0"], Fraction(287, 13))
        self.assertEqual(obs["witness_287_x1"], Fraction(331, 13))
        self.assertTrue(obs["witness_287_satisfies_3D_and_cubic"])
        self.assertTrue(obs["witness_287_separated_by_z_and_23D"])

    def test_subexponential_cubic_gap_and_primitive_two_block_sweep(self) -> None:
        # 1. Verify W = 5, K = 8 is the sole failure and W = 6..400 has ZERO failures!
        self.assertLess(27 * (1 << (5 - 2)) * (13**3), 1 << (3 * 8))
        p3 = 3**6
        for w_val in range(6, 401):
            k_min = p3.bit_length()
            self.assertTrue(check_subexponential_cubic_gap(k_min, w_val))
            self.assertTrue(check_subexponential_cubic_gap(k_min + 1, w_val))
            p3 *= 3

        # 2. Verify IsPrimitiveTwoBlockBroxWitness is False across all candidate (w1, a1, w2, a2)
        # up to W = 30.
        for w_tot in range(5, 31):
            k_min = (3**w_tot).bit_length()
            for k_tot in (k_min, k_min + 1):
                if not ((21**w_tot) < (7**w_tot) * (1 << k_tot) <= (22**w_tot)):
                    continue
                det = (1 << k_tot) - (3**w_tot)
                for w1 in range(2, w_tot):
                    w2 = w_tot - w1
                    for a1 in range(1, k_tot - w_tot):
                        a2 = k_tot - w_tot - a1
                        h0, h1 = two_block_brox_carries(w1, a1, w2, a2)
                        if h0 % det == 0 and h1 % det == 0:
                            self.assertFalse(
                                is_primitive_two_block_brox_witness(
                                    w1, a1, w2, a2, h0 // det, h1 // det
                                )
                            )

    def test_theorem_t11_hercher_subdouble_merger_and_wave3_master_witness(
        self,
    ) -> None:
        sep = verify_hercher_subdouble_merger_separation()
        self.assertGreater(int(sep["checked_3x1_pairs"]), 50)
        self.assertTrue(sep["all_3x1_mergers_ok"])
        self.assertTrue(sep["m3_x0_13_is_one_block_cycle"])
        self.assertTrue(sep["m3_partner_6_reaches_one"])

        # Verify IsWave3SharpenedBroxWitness is False across boundary sweep K <= 12.
        for w1 in range(2, 9):
            max_init = max(0, 10 - w1)
            for init_len in range(max_init + 1):
                k_len = w1 + 2 + init_len
                if k_len < 8:
                    continue
                for init in product([False, True], repeat=init_len):
                    w_tot = w1 + parity_weight(init)
                    if w_tot < 5:
                        continue
                    det = (1 << k_len) - (3**w_tot)
                    if det <= 0:
                        continue
                    rhs = brox_odd_carry(init) + (1 << (init_len + 1))
                    if rhs % det == 0:
                        self.assertFalse(
                            is_wave3_sharpened_brox_witness(w1, init, rhs // det)
                        )


if __name__ == "__main__":
    unittest.main()
