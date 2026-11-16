"""
Unit test suite for Track 2 (`collatz_analysis/cs_sat_lyapunov.py`):
Mixed-Base (2, 3) Collatz Rewriting, Natural/Arctic Matrix Interpretations &
All-Dimension Impossibility, Shifted-Log Modular-Lyapunov Self-Congruent Pumping,
Universal All-Weight 2^w1-Cancellation Sieves (Mod-5184 & Mod-46656),
Multi-Block Exit-Tail Contraction, and Mandatory 3x3 Counter-Model Gate.
"""

from __future__ import annotations

from fractions import Fraction
import unittest

try:
    from collatz_analysis import cs_sat_lyapunov as csl
except ImportError:  # pragma: no cover
    import cs_sat_lyapunov as csl  # type: ignore[no-redef]


class TestMixedCollatzSRS(unittest.TestCase):
    """Tests for the 11-rule mixed binary-ternary Collatz SRS and M2 boundary flip."""

    def test_symbolic_semantics_and_m2_neg5_cycle(self) -> None:
        res = csl.verify_srs_symbolic_semantics()
        for key, val in res.items():
            self.assertTrue(val, msg=f"Failed symbolic SRS property: {key}")

    def test_unique_binary_encoding_and_collatz_simulation(self) -> None:
        self.assertEqual(csl.encode_pos_binary_word(1), ("L", "R"))
        self.assertEqual(csl.srs_eval_framed(("L", "R")), 1)

        for n in range(1, 151):
            w = csl.encode_pos_binary_word(n)
            self.assertEqual(csl.srs_eval_framed(w), n)
            nf, trace, halted = csl.simulate_srs_leftmost(w, max_steps=5000)
            self.assertTrue(halted, msg=f"Did not halt on n={n}")
            self.assertEqual(nf, ("L", "R"))

            # Verify every intermediate rewrite step matches Collatz step on R1/R2
            # and preserves srs_eval on R3..R11
            cur_val = n
            for rname, nxt_w in trace:
                nxt_val = csl.srs_eval_framed(nxt_w)
                if rname in ("R1_even", "R2_odd"):
                    self.assertEqual(nxt_val, csl.collatz_step(cur_val))
                else:
                    self.assertEqual(nxt_val, cur_val)
                cur_val = nxt_val
            self.assertEqual(cur_val, 1)

    def test_negative_msb_boundary_flip_cycles(self) -> None:
        # -5 = ('L', 'B1', 'B1', 'B0', 'R_neg') loops in 9 carry-first SRS steps
        # (and enters an 8-step cycle after 1 step under head-first rule order)
        w_neg5 = csl.encode_neg_binary_word(-5)
        self.assertEqual(w_neg5, ("L", "B1", "B1", "B0", "R_neg"))
        self.assertEqual(csl.srs_eval_framed(w_neg5), -5)
        carry_first = csl.MIXED_COLLATZ_NEG_SRS_RULES[2:] + csl.MIXED_COLLATZ_NEG_SRS_RULES[:2]
        cur = w_neg5
        for step in range(1, 10):
            nxts = csl.srs_one_step_all(cur, rules=carry_first)
            self.assertGreaterEqual(len(nxts), 1)
            _, cur = nxts[0]
            if step < 9:
                self.assertNotEqual(cur, w_neg5)
        self.assertEqual(cur, w_neg5)

        # Also check head-first lasso: step 1 == step 10 == ('L', 'T2', 'B1', 'B0', 'R_neg') (period 9)
        cur_std = w_neg5
        trace_std = [cur_std]
        for _ in range(10):
            _, cur_std = csl.srs_one_step_all(cur_std, rules=csl.MIXED_COLLATZ_NEG_SRS_RULES)[0]
            trace_std.append(cur_std)
        self.assertEqual(trace_std[1], trace_std[10])


class TestMatrixInterpretationsAndImpossibility(unittest.TestCase):
    """Tests for Natural/Arctic matrix certificates and universal impossibility theorems."""

    def test_subsystem_without_odd_step_d1_natural_and_d2_arctic(self) -> None:
        sub_rules, nat_cert, arc_cert = csl.get_subsystem_without_odd_step_certificates()
        self.assertEqual(len(sub_rules), 10)
        self.assertTrue(nat_cert.verify_rules(sub_rules))
        self.assertTrue(arc_cert.verify_rules(sub_rules))

        # Adding R2_odd must fail both certificates
        r2 = csl.MIXED_COLLATZ_SRS_RULES[1]
        self.assertEqual(r2.name, "R2_odd")
        self.assertFalse(nat_cert.orients_rule(r2))
        self.assertFalse(arc_cert.orients_rule(r2))

    def test_interior_and_head_8rule_d2_natural_certificate(self) -> None:
        rules_8, nat_d2 = csl.get_interior_and_head_8rule_natural_certificate()
        self.assertEqual(len(rules_8), 8)
        self.assertTrue(nat_d2.verify_rules(rules_8))

        # Adding right-boundary expansion R11_t2R breaks orientation
        r11 = csl.MIXED_COLLATZ_SRS_RULES[10]
        self.assertEqual(r11.name, "R11_t2R")
        self.assertFalse(nat_d2.orients_rule(r11))

    def test_odd_plus_carry_10rule_2adic_lexicographic_ranking(self) -> None:
        rules_no_r1 = tuple(r for r in csl.MIXED_COLLATZ_SRS_RULES if r.name != "R1_even")
        self.assertEqual(len(rules_no_r1), 10)
        # Test on Mersenne numbers 2^k - 1 (k = 2..9) and general odd numbers
        test_ns = [(1 << k) - 1 for k in range(2, 10)] + [27, 31, 47, 63, 95, 127]
        for n in test_ns:
            cur = csl.encode_pos_binary_word(n)
            prev_rank = csl.odd_plus_carry_10rule_lex_measure(cur)
            steps = 0
            while True:
                nxts = csl.srs_one_step_all(cur, rules=rules_no_r1)
                if not nxts:
                    break
                rname, cur = nxts[0]
                cur_rank = csl.odd_plus_carry_10rule_lex_measure(cur)
                self.assertLess(cur_rank, prev_rank, msg=f"Rank failed to drop on {rname}")
                if rname == "R2_odd":
                    self.assertEqual(cur_rank[0], prev_rank[0] - 1)
                else:
                    self.assertEqual(cur_rank[0], prev_rank[0])
                prev_rank = cur_rank
                steps += 1
            self.assertGreater(steps, 0)

    def test_1d_monotone_natural_affine_impossibility(self) -> None:
        cert = csl.prove_1d_natural_affine_impossibility_core()
        self.assertTrue(cert["farkas_contradiction_c_B1_gt_c_T2_and_c_T2_gt_c_B1"])
        self.assertFalse(cert["lp_m2_feasible"])

    def test_all_dimension_arctic_quadratic_pumping_obstruction(self) -> None:
        for k_max in (0, 1, 2, 5, 10, 20):
            wit = csl.witness_arctic_all_dim_quadratic_pumping(k_max)
            self.assertEqual(wit["actual_steps"], wit["expected_steps"])
            self.assertTrue(wit["halted_at_L_T2m_R"])
            self.assertTrue(wit["strictly_exceeds_arctic_bound"])


class TestModularLyapunovLPAndSelfCongruentPumping(unittest.TestCase):
    """Tests for exact Fraction LP solver and universal self-congruent Syracuse pumping."""

    def test_bezout_pow3_pow2_exact_identity(self) -> None:
        for p in range(0, 12):
            for q in range(0, 10):
                a, b = csl.bezout_pow3_pow2(p, q)
                self.assertGreaterEqual(a, 1)
                self.assertGreaterEqual(b, 0)
                self.assertEqual((3 ** q) * a - (1 << p) * b, 1)

    def test_bounded_weight_vs_unbounded_1run_lp(self) -> None:
        # Capping w <= 1 on mod 16 is feasible, while allowing w >= 4 (15 mod 16) is infeasible!
        feas_w1, beta_w1 = csl.solve_bounded_weight_modular_potential_lp(mod_2_exp=4, w_cap=1)
        self.assertTrue(feas_w1)
        self.assertIsNotNone(beta_w1)

        feas_w4, beta_w4 = csl.solve_bounded_weight_modular_potential_lp(mod_2_exp=4, w_cap=4)
        self.assertFalse(feas_w4)
        self.assertIsNone(beta_w4)

    def test_shifted_piecewise_log_modular_lp_and_eigen_shifts(self) -> None:
        self.assertEqual(csl.block_eigen_shift(1, 1), Fraction(-1))
        self.assertEqual(csl.block_eigen_shift(2, 1), Fraction(5))
        self.assertEqual(csl.block_eigen_shift(3, 1), Fraction(19, 11))

        res_w1 = csl.solve_shifted_piecewise_log_modular_lp(mod_2_exp=4, w_cap=1)
        self.assertTrue(res_w1["zpos_domain_valid_x_ge_3"])
        self.assertTrue(res_w1["zneg_pole_or_flip_at_neg5"])
        self.assertTrue(res_w1["lp_feasible"])

        res_w4 = csl.solve_shifted_piecewise_log_modular_lp(mod_2_exp=4, w_cap=4)
        self.assertTrue(res_w4["zpos_domain_valid_x_ge_3"])
        self.assertTrue(res_w4["zneg_pole_or_flip_at_neg5"])
        self.assertFalse(res_w4["lp_feasible"])

        # Verify self-congruent pumping witness strictly defeats any shifted-log
        # potential V(x) = alpha_r * log(x + c_r) + beta_r even for huge |c_r| <= 10^6!
        wit = csl.construct_self_congruent_syracuse_pumping_witness(
            exp2_A=6,
            exp3_B=4,
            s_blocks=4,
            min_growth_G=3,
            min_x1_floor=1_000_000,
        )
        self.assertGreater(int(wit["x_1"]), 1_000_000)
        self.assertTrue(wit["mod_self_congruent"])
        self.assertGreater(int(wit["x_end"]) - 1_000_000, int(wit["x_1"]) - 1_000_000)

    def test_self_congruent_syracuse_pumping_witnesses(self) -> None:
        params = [
            (4, 4, 3, 2),    # Mod-1296 & Mod-5184 at s=3
            (4, 4, 4, 5),    # Mod-46656 at s=4, growth > 5x
            (6, 4, 4, 10),   # Mod-5184 & Mod-46656 at s=4, growth > 10x
            (6, 6, 4, 3),    # Exact Mod-46656 self-congruence!
            (8, 7, 5, 20),   # Higher 2^8 * 3^7 modulus, s=5 blocks, growth > 20x
        ]
        for exp_a, exp_b, s_blocks, growth_g in params:
            wit = csl.construct_self_congruent_syracuse_pumping_witness(
                exp2_A=exp_a,
                exp3_B=exp_b,
                s_blocks=s_blocks,
                min_growth_G=growth_g,
            )
            self.assertTrue(wit["collatz_iter_matches"])
            self.assertTrue(wit["all_a_eq_1"])
            self.assertTrue(wit["mod_self_congruent"])
            self.assertTrue(wit["exceeds_growth_G"])
            self.assertTrue(wit["survives_mod1296_start"])
            self.assertTrue(wit["survives_mod1296_end"])
            self.assertTrue(wit["survives_mod5184_start"])
            self.assertTrue(wit["survives_mod5184_end"])
            if s_blocks >= 4:
                self.assertTrue(wit["survives_mod46656_start"])
                self.assertTrue(wit["survives_mod46656_end"])
                self.assertTrue(wit["survives_mod373248_start"])
                self.assertTrue(wit["survives_mod373248_end"])


class TestUniversalAllWeightCancellationAndMod46656Sieve(unittest.TestCase):
    """Tests for the 2^w1-cancellation master identity, Mod-5184/46656 sieve, and exit-tail forcing."""

    def test_sieve_exact_counts_and_strict_refinement(self) -> None:
        counts = csl.compute_sieved_survival_counts()
        self.assertEqual(counts["mod1296_prev"], (131, 1296, Fraction(131, 1296)))
        self.assertEqual(counts["mod1296_all_weight"], (129, 1296, Fraction(43, 432)))
        self.assertEqual(counts["mod5184"], (301, 5184, Fraction(301, 5184)))
        self.assertEqual(counts["mod46656"], (2674, 46656, Fraction(1337, 23328)))

        # Strict monotone density shrinkage: 5/36 > 131/1296 > 129/1296 > 301/5184 > 2674/46656
        self.assertGreater(counts["mod36"][2], counts["mod1296_prev"][2])
        self.assertGreater(counts["mod1296_prev"][2], counts["mod1296_all_weight"][2])
        self.assertGreater(counts["mod1296_all_weight"][2], counts["mod5184"][2])
        self.assertGreater(counts["mod5184"][2], counts["mod46656"][2])

        # Inclusion chain: Mod46656 => Mod5184 => Mod1296
        for n in range(5184):
            if csl.is_surviving_mod5184_class(n):
                self.assertTrue(csl.is_surviving_mod1296_class(n))

    def test_all_weight_head_cancellation_across_unbounded_w1(self) -> None:
        # Test w1 from 2 up to 18 on numbers n_val = 2^w1 * u1 - 1 with a1 = 1
        heads = (
            csl.UHEAD_MOD81_60,
            csl.UHEAD_MOD729_45,
            csl.UHEAD_MOD729_159,
            csl.UHEAD_MOD729_330,
        )
        for w1 in range(2, 19):
            # Pick u1 odd such that (3^w1 * u1 - 1) % 4 == 2, i.e. u1 % 4 == 3^(w1+1) % 4
            u1 = 3 if ((w1 + 1) % 2 == 1) else 1
            n_val = (1 << w1) * u1 - 1
            for u_head in heads:
                res = csl.verify_all_weight_head_cancellation_identity(u_head, n_val)
                self.assertTrue(res["eq1_step_w1_plus_2"])
                self.assertTrue(res["eq2_scaled"])
                self.assertTrue(res["eq3_carry_decomp"])
                self.assertTrue(res["eq4_exact_cancellation"])

    def test_universal_exclusions_small_q_and_high_weights(self) -> None:
        # 1. Check q = 0..25 on every newly excluded arithmetic progression!
        for q in range(26):
            for n_cand in (
                32 * q + 11,
                32 * q + 23,
                64 * q + 15,
                81 * q + 60,
                729 * q + 45,
                729 * q + 159,
                729 * q + 330,
                729 * q + 433,
                729 * q + 604,
            ):
                if n_cand <= 1:
                    continue
                wit = csl.witness_new_universal_exclusions_for_n(n_cand)
                if wit["kind"] == "descent":
                    self.assertGreater(int(wit["val"]), 0)
                    self.assertLess(int(wit["val"]), n_cand)
                else:
                    self.assertTrue(wit["valid"], msg=f"Merger invalid on n={n_cand}: {wit}")

        # 2. Explicitly test high-weight w1 >= 5..12 instances of 60 mod 81 and {45,159,330} mod 729
        #    (which were completely unreachable by any fixed-horizon K <= 4 table like 1275 mod 1296!)
        for w1 in range(5, 13):
            inv2w1_81 = pow(1 << w1, -1, 81)
            u1_81 = (61 * inv2w1_81) % 81
            # Lift u1 ≡ u1_81 (mod 81) and u1 odd with a1 = 1
            req_mod4 = 3 if ((w1 + 1) % 2 == 1) else 1
            while u1_81 % 4 != req_mod4:
                u1_81 += 81
            n_high_60 = (1 << w1) * u1_81 - 1
            self.assertEqual(n_high_60 % 81, 60)
            wit60 = csl.witness_new_universal_exclusions_for_n(n_high_60)
            self.assertEqual(wit60["kind"], "coalescence")
            self.assertTrue(wit60["valid"])

            for r729 in (45, 159, 330):
                inv2w1_729 = pow(1 << w1, -1, 729)
                u1_729 = ((r729 + 1) * inv2w1_729) % 729
                while u1_729 % 4 != req_mod4:
                    u1_729 += 729
                n_high_729 = (1 << w1) * u1_729 - 1
                self.assertEqual(n_high_729 % 729, r729)
                wit729 = csl.witness_new_universal_exclusions_for_n(n_high_729)
                self.assertEqual(wit729["kind"], "coalescence")
                self.assertTrue(wit729["valid"])

    def test_multi_block_w1_4_and_5_exit_tail_a2_forcing(self) -> None:
        tested_w1_4_w2_2_a2_ge2 = 0
        tested_w1_5_w2_1_a2_ge2 = 0
        for u1 in range(1, 400, 2):
            # Case w1 = 4: n = 16 * u1 - 1
            n4 = 16 * u1 - 1
            w1, _, a1, x2 = csl.syracuse_block(n4)
            if w1 == 4 and a1 == 1:
                w2, _, a2, _ = csl.syracuse_block(x2)
                if w2 in (1, 2):
                    res = csl.verify_w1_4_and_5_exit_tail_a2_forcing(n4)
                    self.assertTrue(res["x2_gt_2n"])
                    self.assertTrue(res["x_last_le_4n"])
                    if a2 >= 2:
                        self.assertTrue(res["a2_ge_2_merged_with_smaller"])
                        if w2 == 2:
                            tested_w1_4_w2_2_a2_ge2 += 1

            # Case w1 = 5: n = 32 * u1 - 1
            n5 = 32 * u1 - 1
            w1b, _, a1b, x2b = csl.syracuse_block(n5)
            if w1b == 5 and a1b == 1:
                w2b, _, a2b, _ = csl.syracuse_block(x2b)
                if w2b == 1:
                    res5 = csl.verify_w1_4_and_5_exit_tail_a2_forcing(n5)
                    self.assertTrue(res5["x2_gt_2n"])
                    self.assertTrue(res5["x_last_le_4n"])
                    if a2b >= 2:
                        self.assertTrue(res5["a2_ge_2_merged_with_smaller"])
                        tested_w1_5_w2_1_a2_ge2 += 1

        self.assertGreater(tested_w1_4_w2_2_a2_ge2, 5)
        self.assertGreater(tested_w1_5_w2_1_a2_ge2, 5)


class TestWave2UpperTriangularMod373248AndCrossTrack(unittest.TestCase):
    """Wave 2 tests for T2.4 (d>=1 collapse & d=2 triangular impossibility), T2.5 (Mod-373248), and T2.6."""

    def test_t24_upper_triangular_collapse_and_d2_impossibility(self) -> None:
        res = csl.verify_d2_upper_triangular_impossibility_algebraic()
        for key, ok in res.items():
            self.assertTrue(ok, msg=f"Wave 2 T2.4 check failed: {key}")

    def test_t25_mod373248_exact_counts_and_27_floor(self) -> None:
        counts = csl.compute_sieved_survival_counts()
        self.assertEqual(counts["mod186624"], (6112, 186624, Fraction(191, 5832)))
        self.assertEqual(counts["mod373248"], (10314, 373248, Fraction(191, 6912)))
        self.assertLess(counts["mod373248"][2], counts["mod186624"][2])
        self.assertLess(counts["mod186624"][2], counts["mod46656"][2])

        # Every n in 0..26 is excluded; 27 is the exact minimal positive survivor!
        for n_small in range(0, 27):
            self.assertFalse(csl.is_surviving_mod373248_class(n_small))
        self.assertTrue(csl.is_surviving_mod373248_class(27))

        # Inclusion chain: Mod373248 => Mod46656 => Mod5184 => Mod1296
        for n in range(2, 4000):
            if csl.is_surviving_mod373248_class(n):
                self.assertTrue(csl.is_surviving_mod46656_class(n))
            else:
                wit = csl.witness_mod512_and_mod373248_exclusion(n)
                if wit["kind"] == "descent":
                    self.assertGreater(int(wit["val"]), 0)
                    self.assertLess(int(wit["val"]), n)
                else:
                    self.assertTrue(wit["valid"], msg=f"Invalid merger witness at n={n}: {wit}")

    def test_t26_cross_track_mod373248_core_quotient_contraction(self) -> None:
        # Regression lock for CEGAR #18: K >= 1 (`1 <= K`) is mandatory because
        # minimal Mod-373248 survivor n = 27 has 27 % 3 == 0 (Garden-of-Eden):
        # at K = 0, collatz_iter(0, 27) = 27 violates x % 3 != 0, and naive total
        # floor quotients (17 for u=[True], 14 for u=[True,False,True,True]) do NOT coalesce!
        self.assertTrue(csl.is_surviving_mod373248_class(27))
        self.assertEqual(csl.collatz_iter(0, 27) % 3, 0)
        with self.assertRaises(ValueError):
            csl.exact_backward_quotient_py(csl.collatz_iter(0, 27), (True,), q=0)
        self.assertNotEqual(csl.collatz_iter(1, (2 * 27 - 1) // 3), 27)
        self.assertNotEqual(csl.collatz_iter(4, (16 * 27 - 31) // 27), 27)
        # Whereas for every K >= 1, collatz_iter(K, 27) % 3 != 0!
        for k_pos in range(1, 20):
            self.assertNotEqual(csl.collatz_iter(k_pos, 27) % 3, 0)

        # Verify every Mod-373248 survivor in [27, 1500] satisfies
        # Mod373248CoreQuotientContractionProp and Mod373248CoreForestQuotientCollisionProp
        # with K >= 1 and core word u = [True] (1...1)
        survivors_checked = 0
        for n in range(27, 1501):
            if not csl.is_surviving_mod373248_class(n):
                continue
            survivors_checked += 1
            chk = csl.verify_mod373248_core_quotient_contraction_at_n(n)
            self.assertTrue(chk["n_ge_27"])
            self.assertTrue(chk["K_ge_1"])
            self.assertTrue(chk["x_K_mod3_ne_0"])
            self.assertTrue(chk["contraction_q0_ok"])
            self.assertTrue(chk["forest_collision_ok"])
        self.assertGreater(survivors_checked, 35)


class TestCounterModel3x3Gate(unittest.TestCase):
    """Tests for the Mandatory 3x3 Counter-Model Gate (Z^+, M1=Q_(2)^+, M2=Z^-, M3=5x+1)."""

    def test_full_3x3_counter_model_gate(self) -> None:
        audit = csl.audit_3x3_counter_model_gate()
        for key, passed in audit.items():
            self.assertTrue(passed, msg=f"3x3 Counter-Model Gate failed check: {key}")


class TestWave3MyhillNerodeHigherDimAndInfiniteSieve(unittest.TestCase):
    """Wave 3 tests for T2.7 (3^w & 2^w Myhill-Nerode DFA barrier), T2.8 (d>=1 collapse), and T2.9 (infinite families)."""

    def test_t27_binary_gap_2w_and_full_3w_myhill_nerode_dfa_refuter(self) -> None:
        # 1. Binary-gap fixed-weight 2^w family: pairwise distinct shifts & 0^k separation for w = 1..6
        for w in range(1, 7):
            words = [
                csl.binary_gap_weight_word(bits)
                for bits in __import__("itertools").product((False, True), repeat=w)
            ]
            self.assertEqual(len(words), 1 << w)
            shifts = [csl.canonical_suffix_shift_at_one(u) for u in words]
            self.assertEqual(len(set(shifts)), 1 << w)
            # Check pairwise 0^k separation on w <= 4
            if w <= 4:
                for i in range(len(words)):
                    for j in range(i + 1, len(words)):
                        suf = csl.distinguishing_zero_suffix_for_one_eq(words[i], words[j])
                        self.assertNotEqual(
                            csl.is_valid_one_equation_word(words[i] + suf),
                            csl.is_valid_one_equation_word(words[j] + suf),
                        )

        # 2. Full 3^w witness family: exact cardinality 3^w, duplicate-free, pairwise 0^k separated
        for w in range(1, 5):
            fam = csl.myhill_nerode_pow3_witness_family(w)
            self.assertEqual(len(fam), 3 ** w)
            self.assertEqual(len(set(fam)), 3 ** w)
            for i in range(len(fam)):
                for j in range(i + 1, len(fam)):
                    suf = csl.distinguishing_zero_suffix_for_one_eq(fam[i], fam[j])
                    self.assertNotEqual(
                        csl.is_valid_one_equation_word(fam[i] + suf),
                        csl.is_valid_one_equation_word(fam[j] + suf),
                    )

        # 3. Constructive refutation of arbitrary DFAs across N = 1..26 states
        for n_states in (1, 2, 5, 8, 9, 15, 26):
            ref = csl.refute_arbitrary_dfa_on_one_equation(
                n_states=n_states,
                transition_fn=lambda q, bit, m=n_states: (2 * q + (1 if bit else 0) + 1) % m,
                start_state=0,
                accept_states=[q for q in range(0, n_states, 2)],
            )
            self.assertTrue(ref["dfa_refuted"], msg=f"DFA refuter failed at N={n_states}: {ref}")

    def test_t28_all_dim_coord_monotone_collapse_and_sub6_sharpness(self) -> None:
        res = csl.verify_all_dim_coord_monotone_upper_tri_collapse(max_dim_test=6)
        for key, ok in res.items():
            self.assertTrue(ok, msg=f"Wave 3 T2.8 check failed: {key}")

    def test_t29_infinite_dyadic_and_triadic_excluded_families_and_3x3_gate(self) -> None:
        # 1. Infinite dyadic family across k = 2..16 and q = 0..4 (including q = 0 boundary!)
        for k in range(2, 17):
            for q in range(0, 5):
                wit = csl.witness_dyadic_parametric_exclusion(k, q)
                self.assertTrue(wit["v2_n_plus_1_eq_k"])
                self.assertTrue(wit["strictly_smaller_pos"])
                self.assertTrue(wit["coalesces_k2_k1"])
                self.assertTrue(wit["survives_mod512_for_k_ge_8"])

        # Pairwise disjointness of dyadic classes across k = 2..16
        dyadic_classes = [csl.dyadic_entry_excluded_residue(k) for k in range(2, 17)]
        for i in range(len(dyadic_classes)):
            r_i, mod_i = dyadic_classes[i]
            for j in range(i + 1, len(dyadic_classes)):
                r_j, _ = dyadic_classes[j]
                self.assertNotEqual(r_j % mod_i, r_i)

        # 2. Infinite closed-form triadic family across k = 3..14 and q = 0..3
        triadic_classes = []
        for k in range(3, 15):
            r_k, mod_k = csl.triadic_backward_excluded_residue(k)
            triadic_classes.append((r_k, mod_k))
            for q in range(0, 4):
                wit = csl.witness_triadic_parametric_exclusion(k, q)
                self.assertTrue(wit["exact_div27"])
                self.assertTrue(wit["r_lt_modulus"])
                self.assertTrue(wit["r_mod729_eq_361"])
                self.assertTrue(wit["strictly_smaller_pos"])
                self.assertTrue(wit["coalesces_3k10_0"])

        # Pairwise disjointness of triadic classes across k = 3..14
        for i in range(len(triadic_classes)):
            r_i, mod_i = triadic_classes[i]
            for j in range(i + 1, len(triadic_classes)):
                r_j, _ = triadic_classes[j]
                self.assertNotEqual(r_j % mod_i, r_i)

        # CRT check: for every k >= 8 (dyadic) and k >= 3 (triadic), produces excluded integers
        # strictly INSIDE IsSurvivingMod373248Class!
        for k_d in (8, 9, 10, 11):
            r_d, m_d = csl.dyadic_entry_excluded_residue(k_d)
            # Combine with 1 mod 729 (survives Mod-729!)
            n_crt = r_d + m_d * ((1 - r_d) * pow(m_d, -1, 729) % 729)
            self.assertTrue(csl.is_surviving_mod373248_class(n_crt))
            wit_d = csl.witness_dyadic_parametric_exclusion(k_d, (n_crt - r_d) // m_d)
            self.assertTrue(wit_d["coalesces_k2_k1"] and wit_d["strictly_smaller_pos"])

        for k_t in (3, 4, 5, 6):
            r_t, m_t = csl.triadic_backward_excluded_residue(k_t)
            # Combine with 27 mod 512 (survives Mod-512!)
            n_crt = r_t + m_t * ((27 - r_t) * pow(m_t, -1, 512) % 512)
            self.assertTrue(csl.is_surviving_mod373248_class(n_crt))
            wit_t = csl.witness_triadic_parametric_exclusion(k_t, (n_crt - r_t) // m_t)
            self.assertTrue(wit_t["coalesces_3k10_0"] and wit_t["strictly_smaller_pos"])

        # 3. Wave 3 3x3 Counter-Model Gate
        gate3 = csl.audit_wave3_3x3_counter_model_gate()
        for key, ok in gate3.items():
            self.assertTrue(ok, msg=f"Wave 3 3x3 gate failed: {key}")


if __name__ == "__main__":
    unittest.main()
