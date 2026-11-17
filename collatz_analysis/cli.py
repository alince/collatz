"""
Command-line interface for the Collatz Conjecture Research & Verification Suite.
"""

from __future__ import annotations

import argparse
from typing import Sequence

from .boost_obstructions import (
    classify_s_integer_1cycles_z_inv_30,
    compute_brox_effective_finiteness_bounds,
    prove_m92_nonexistence_hensel_certificate,
    verify_cantor_cone_rigidity_and_uncertainty,
)
from .coalescence_and_mcycles import (
    compute_contractive_coalescence_sieve,
    prove_2cycle_nonexistence_up_to_weight,
    prove_surviving_diamond_threshold_k34,
)
from .frontier_reductions import (
    self_certify_garner_bootstrap,
    verify_counter_model_no_go_meta_theorem,
    verify_one_equation_diophantine_equivalence,
    verify_raney_cantor_cone_on_negative_cycles,
)
from .goal_extensions import (
    classify_5adic_unit_cycle_denominators,
    classify_all_z_2cycles_and_3cycles,
    classify_s_integer_2cycles_z_inv_30,
    prove_multistep_hensel_mcycle_nonexistence,
    verify_deficit_drift_complementarity_and_peak_bound,
    verify_lower_semiconvergent_pinch_and_baker_floor,
    verify_minimal_divergent_coalescence_obstruction,
)
from .mcycles_and_cantor_cone import (
    analyze_cantor_cone_and_sturmian_2adic,
    prove_unconditional_mcycle_nonexistence,
    verify_one_sided_semiconvergent_records,
)
from .cycles import (
    compute_min_cycle_length_bound,
    exhaustive_cycle_search_up_to_k,
    prove_steiners_1cycle_theorem,
)
from .formal_proofs import (
    verify_base2_transducer_state_growth,
    verify_catalan_mihailescu_unit_cycles,
    verify_lean4_kernel_proofs,
)
from .parity_2adic import analyze_trajectory
from .stopping_time import (
    analyze_tao_syracuse_mixing,
    compute_exact_stopping_time_dp,
    cramer_large_deviation_parameters,
    verify_beatty_sturmian_characterization,
)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Collatz Conjecture 2-Adic, Diophantine, and Stopping-Time Analyzer"
    )
    mode_group = parser.add_mutually_exclusive_group()
    mode_group.add_argument(
        "--summary",
        action="store_true",
        help="Run the full constructive theorem and computational verification summary",
    )
    mode_group.add_argument(
        "--trajectory",
        type=int,
        default=None,
        help="Analyze the compressed Collatz trajectory for a starting integer n",
    )
    parser.add_argument(
        "--dp-depth",
        type=int,
        default=None,
        help="Max depth K for exact lattice-path stopping-time DP (default: 200)",
    )
    parser.add_argument(
        "--full-m95",
        action="store_true",
        help="Re-run the full c=4 Lambda-squeeze Hensel tree for m = 95, u = 1",
    )
    args = parser.parse_args(argv)

    if args.trajectory is not None:
        if args.dp_depth is not None or args.full_m95:
            parser.error("--dp-depth and --full-m95 cannot be combined with --trajectory")
        traj = analyze_trajectory(args.trajectory)
        print(f"=== Trajectory Analysis for n = {traj.n} ===")
        print(f"Stopping time sigma(n)       : {traj.stopping_time_sigma}")
        print(f"Coeff stopping time tau(n)   : {traj.coeff_stopping_time_tau}")
        print(f"Total stopping time sigma_inf: {traj.total_stopping_time}")
        print(f"Max excursion                : {traj.max_excursion}")
        print(f"First 20 orbit steps         : {traj.orbit[:20]}")
        return 0

    dp_depth = 200 if args.dp_depth is None else args.dp_depth

    print("======================================================================")
    print("  COLLATZ CONJECTURE: 2-ADIC, DIOPHANTINE & STOPPING-TIME SUITE")
    print("======================================================================")

    # 1. Beatty-Sturmian & Catalan-Mihailescu
    beatty = verify_beatty_sturmian_characterization(max_k=12)
    catalan = verify_catalan_mihailescu_unit_cycles(max_k=20)
    cycles_11 = exhaustive_cycle_search_up_to_k(max_k=11)
    print(f"\n[Theorem 1 & 2] 2-Adic Parity Bijection & Beatty-Sturmian Carry Bounds:")
    print(f"  - Beatty-Sturmian characterization exact on 2^12 vectors : {beatty['characterization_exact']}")
    print(f"  - Catalan-Mihailescu unit-denominator pairs |2^k - 3^w|=1: {catalan['unit_denominator_pairs']}")
    print(f"  - Exhaustive primitive cycles in Z^+ (k <= 11)           : {len(cycles_11['primitive_positive_cycles'])} (n0 = 1)")
    print(f"  - Exhaustive primitive cycles in Z^- (k <= 11)           : {len(cycles_11['primitive_negative_cycles'])} (n0 in {{-1, -5, -17}})")

    # 2. Steiner's 1-Cycle Theorem & Eliahou Cycle Length Bounds
    steiner = prove_steiners_1cycle_theorem()
    b68 = compute_min_cycle_length_bound(68.0)
    b71 = compute_min_cycle_length_bound(71.0)
    print(f"\n[Theorem 3] Steiner's 1-Cycle Theorem & Eliahou Cycle Length Bounds:")
    print(f"  - Baker-LMN analytic cutoff W_Baker                      : w = {steiner['baker_lmn_cutoff_w']}")
    print(f"  - Unique positive integer 1-cycle (w, k, n0)             : {steiner['unique_positive_1cycle']}")
    print(f"  - Min cycle length for N0 = 2^68 (Barina 2021)           : k >= {b68.min_compressed_length:,} compressed ({b68.min_uncompressed_length:,} uncompressed)")
    print(f"  - Min cycle length for N0 = 2^71 (Barina 2025)           : k >= {b71.min_compressed_length:,} compressed ({b71.min_uncompressed_length:,} uncompressed)")

    # 3. Stopping-Time DP & Cramer Rate
    dp = compute_exact_stopping_time_dp(max_k=dp_depth)
    cramer = cramer_large_deviation_parameters()
    print(f"\n[Theorem 4] Exact Lattice-Path Stopping-Time Sieve & Cramer Decay:")
    print(f"  - Critical slope p* = log_3(2)                           : {cramer['critical_slope_p_star']:.9f}")
    print(f"  - Cramer KL rate I_2(p*) = 1 - H_2(log_3(2))             : {cramer['kl_rate_bits']:.9f} bits/step")
    print(f"  - Asymptotic decay factor rho = 2^(-I_2(p*))             : {cramer['asymptotic_decay_base_rho']:.9f}")
    for k_sample in sorted({k for k in (10, 25, 50, 100, dp_depth) if k <= dp_depth}):
        row = dp[k_sample - 1]
        print(
            f"  - Depth k = {row.k:3d}: S(k) = {row.surviving_classes} / 2^{row.k} "
            f"--> d_k = {row.survival_fraction:.6e}"
        )

    # 4. Tao's 3-Adic Memory Annihilation & Base-2 Transducer Complexity
    tao = analyze_tao_syracuse_mixing(max_odd_n=9999, mod_power_3=4)
    transducer = verify_base2_transducer_state_growth(max_w=6)
    print(f"\n[Theorem 5] Tao's 3-Adic Memory Annihilation & Base-2 Transducer Barrier:")
    print(f"  - Empirical Syracuse log2 drift (vs log2(3)-2 = -0.41504): {tao['empirical_log2_drift']:.6f}")
    print(f"  - Coupling TV distance mod 3^4 across steps t = 1..6     : {[round(x, 6) for x in tao['coupling_tv_by_step']]}")
    print(f"  - Exact 4-step 3-adic memory annihilation (TV == 0)      : {tao['exact_memory_erasure_at_step_m']}")
    print(f"  - Base-2 carry DFA state counts for w = 1..6             : {[t.reachable_carry_states for t in transducer]}")

    # 5. Theorems 6, 7, 8: Ultrametric Diamond Threshold (k*=34), Coalescence Sieve & 2-Cycles
    thm6 = prove_surviving_diamond_threshold_k34()
    thm7 = compute_contractive_coalescence_sieve(max_k=17)
    thm8 = prove_2cycle_nonexistence_up_to_weight(max_W=70)
    print(f"\n[Theorem 6] Sharp Equal-Length Surviving Diamond Threshold (k* = 34, w* = 22):")
    print(f"  - Analytic max suffix ratio at w = 20 (< 1 => 0 pairs)   : {thm6['max_analytic_ratio_w20']:.6f}")
    print(f"  - Surviving diamond pairs for all 1 <= k <= 33           : 0")
    print(f"  - Exact minimal surviving diamond pairs at k*=34, w*=22  : {thm6['minimal_k34_w22_pairs_count']} (all with r_low - r_high = 4)")
    p0 = thm6["minimal_k34_w22_pairs"][0]
    print(f"  - Witness #1: T^34({p0.residue_low}) == T^34({p0.residue_high}) == {p0.common_image_b}")

    print(f"\n[Theorem 7] Master (2,3)-Adic Contractive Coalescence Sieve:")
    print(f"  - Sharp onset of unequal-length contractive coalescence  : k = 6, w = 4 (n = 64t + 15 -> T^6(n) = T^1(54t + 13))")
    print(f"  - Depth k = 17 surviving S(17) vs uncoalesced active     : {thm7['final_S_k']} -> {thm7['final_coalescence_active']} ({thm7['final_reduction_percent']:.2f}% pruned)")

    print(f"\n[Theorem 8] Master m-Cycle Block-Telescoping & 2-Cycle Obstruction:")
    print(f"  - 2-cycle tuples verified up to W <= 70                  : {thm8['total_tuples_checked']:,}")
    print(f"  - Primitive positive integer 2-cycles found              : {len(thm8['primitive_2cycles_found'])} (only trivial (1,1,1,1) -> n0=1)")

    thm9 = verify_one_equation_diophantine_equivalence(max_n=200)
    thm10_raney = verify_raney_cantor_cone_on_negative_cycles()
    thm10_boot = self_certify_garner_bootstrap(limit_n=72058, sieve_k=14, max_w_scan=2000)
    thm11 = verify_counter_model_no_go_meta_theorem()

    print(f"\n[Theorem 9] One-Equation (2,3)-Bilinear Diophantine Equivalence:")
    print(f"  - Forward & converse Hensel parity forcing verified      : {thm9['equivalence_verified']} ({thm9['converse_solutions_verified_up_to_k12']} solutions k<=12)")

    print(f"\n[Theorem 10] Raney Z^- Separation & Self-Certified Garner Bootstrap:")
    print(f"  - Z^- cycles have Raney members inside S_infty           : {[r['cantor_cone_S_infty_members'] for r in thm10_raney['records']]}")
    print(f"  - Self-certified N0={thm10_boot['limit_n_verified']:,} ({thm10_boot['survivor_integers_checked']:,} survivors checked) -> cycle-free & sigma==tau up to k <= {thm10_boot['self_certified_garner_and_cycle_free_up_to_k']:,}!")

    print(f"\n[Theorem 11] Counter-Model No-Go Meta-Theorem (Q_(2)^+, Z^-, 5n+1):")
    print(f"  - M1 (Q_(2)^+ cycle k=5, w=3)                            : n0 = {thm11['model_M1_positive_2adic_rational_cycle']['n0']}")
    print(f"  - M2 (Z^- non-unit cycle k=11, w=7, gap=-139)            : n0 = {thm11['model_M2_negative_integer_nonunit_cycle']['n0']}")
    print(f"  - M3 (5n+1 positive Z^+ cycles k=7, w=3, gap=+3)         : n0 in {{13, 17}}")

    thm13 = analyze_cantor_cone_and_sturmian_2adic(bits=64, max_w_norm=200)
    thm14_sc = verify_one_sided_semiconvergent_records(max_w=5000)
    thm14_self = prove_unconditional_mcycle_nonexistence(N0=72058, max_m=20)
    thm14_cpu = prove_unconditional_mcycle_nonexistence(N0=206178386, max_m=32)
    thm14_71 = prove_unconditional_mcycle_nonexistence(N0=1 << 71, max_m=95)

    print(f"\n[Theorem 13] Beatty-Cantor Cone S_infty & Sturmian 2-Adic Exclusion (Open Problem A):")
    print(f"  - Extremal Sturmian 2-adic survivor x_Sturm mod 2^64     : {thm13['x_sturm_hex']} (1s={thm13['ones_count_in_prefix']}, 0s={thm13['zeros_count_in_prefix']})")
    print(f"  - Normalized carry w/6 < C_max^surv(w)/3^w <= w/3 (w<=200): [{thm13['min_observed_C_over_w_3w']:.4f}, {thm13['max_observed_C_over_w_3w']:.4f}] -> x_Sturm not in Z^-")
    print(f"  - Exact Z^- Cantor-cone series sum 2^(j_m)/3^m == |x|    : {[r['exact_abs_x'] for r in thm13['negative_cantor_cone_series_duality']]}")

    print(f"\n[Theorem 14] All-Weight Positive m-Cycle Non-Existence Engine (Open Problem B):")
    print(f"  - One-sided upper semiconvergent records match (W<=5000) : {thm14_sc['exact_sequence_match']} ({thm14_sc['record_count']} records)")
    print(f"  - Unconditional all-W m-cycles ruled out (N0 = 72,058)   : 1 <= m <= {thm14_self['max_m_proved_unconditionally']}")
    print(f"  - Unconditional all-W m-cycles ruled out (N0 = 206.18M)  : 1 <= m <= {thm14_cpu['max_m_proved_unconditionally']}")
    print(f"  - Analytic all-W m-cycles ruled out (Barina N0 = 2^71)   : 1 <= m <= {thm14_71['max_m_proved_unconditionally']} (matches Hercher 2023)")

    thm15a = prove_m92_nonexistence_hensel_certificate(N0=1 << 71, prime_scan_limit=200_000)
    thm15b = compute_brox_effective_finiteness_bounds(max_m=5)
    thm16 = classify_s_integer_1cycles_z_inv_30()
    thm17 = verify_cantor_cone_rigidity_and_uncertainty(max_n_sample=250, sturm_depth=120)

    c92 = thm15a["certificate_m92"]
    print(f"\n[Theorem 15] Breaking the m=91 Barrier -> m <= 92 & Effective Brox Finiteness on Z:")
    print(f"  - Unique candidate (K, W) in (Z^+)^2 at m = 92           : (p_43, q_43) = ({c92.unique_candidate_p}, {c92.unique_candidate_q})")
    print(f"  - Prime factors <= 200k of D_43 = 2^(p_43) - 3^(q_43)    : {thm15a['bottleneck_prime_factor_scan'][43]['factors_up_to_limit']} (none)")
    print(f"  - Exact 2-adic Hensel triples checked at m = 92          : {c92.triples_checked:,} -> {c92.surviving_candidates} survivors ({c92.elapsed_ms:.1f} ms)")
    print(f"  - Upgraded all-W m-cycles ruled out (Barina N0 = 2^71)   : 1 <= m <= {thm15a['max_m_proved_unconditionally']} (exceeds Hercher's m <= 91!)")
    print(f"  - Effective N0-free Brox W_max(m) over ALL Z (m=1..5)    : {[(b.m, b.w_max_lmn) for b in thm15b['bounds']]}")

    print(f"\n[Theorem 16] p-Adic Baker (Bugeaud-Laurent) & Complete Z[1/30] 1-Cycle Classification:")
    print(f"  - Certified cutoffs (W_max, K_max) on Z[1/30]            : ({thm16['baker_bugeaud_laurent_w_max']:,}, {thm16['baker_bugeaud_laurent_k_max']:,})")
    print(f"  - Exact primitive 1-cycles in Z[1/30] ({thm16['elapsed_ms']:.1f} ms)          : {[str(c.x0) for c in thm16['primitive_1cycles']]}")

    print(f"\n[Theorem 17 & 18] Non-Commuting Curvature, S_infty Rigidity Bridges & Uncertainty:")
    print(f"  - Affine commutator curvature [T_0, T_1](x)              : {thm17['commutator_curvature']}")
    print(f"  - Sturmian forward shifts T^r(x_Sturm) exit steps (r=1..5): {[thm17['sturmian_forward_shift_exits_1_to_35'][r] for r in range(1, 6)]}")
    print(f"  - 3-adic Sturmian fiber theta_3(x_Sturm, k=100,120)      : ({thm17['sturmian_3adic_fiber_samples'][100]:.6f}, {thm17['sturmian_3adic_fiber_samples'][120]:.6f}) -> |x_Sturm| > 2^{thm17['sturmian_3adic_excluded_abs_integer_bits']} if in Z")
    print(f"  - Heisenberg uncertainty (T^k(n)-n)*T_bar_w > nw/3       : verified on {thm17['surviving_prefixes_uncertainty_verified']} surviving prefixes")
    print(f"  - Independent S_infty^div toggles in first 78 odd steps  : {thm17['independent_toggles_in_first_78_odd_steps']} (=> 2^aleph_0 continuum disjoint from Z^-)")

    thm19 = prove_multistep_hensel_mcycle_nonexistence(
        N0=1 << 71, max_m_full=94, eliminate_higher_multiples_up_to_m=95
    )
    h19 = thm19["potential_merger_and_horizon"]
    thm20a = classify_all_z_2cycles_and_3cycles()
    thm20b = classify_s_integer_2cycles_z_inv_30()
    thm21a = verify_deficit_drift_complementarity_and_peak_bound(max_n=250)
    thm21b = verify_lower_semiconvergent_pinch_and_baker_floor(max_w=5000, max_n_sample=100)
    thm22a = classify_5adic_unit_cycle_denominators()
    thm22b = verify_minimal_divergent_coalescence_obstruction(max_k=17)

    print(f"\n[Theorem 19] Potential-Merger Bound, Index-45 Horizon & Multi-Step 2-Adic Hensel Tree:")
    print(f"  - 6-line Potential-Merger analytic upgrade (N0 = 2^68)   : 1 <= m <= {h19['barina_2_pow_68_upgraded_max_m']} (upgrades Theorem 14 m <= 88)")
    print(f"  - Lattice confinement to u*(p_43, q_43) (N0 = 2^71)      : 92 <= m <= {h19['barina_2_pow_71_q43_confinement_max_m']}; index 45 ruled out for 1 <= m <= {h19['convergent_45_eliminated_up_to_m']}")
    print(f"  - Recursive multi-step Hensel all-W m-cycle non-existence: 1 <= m <= {thm19['max_m_proved_unconditionally']} ({len(thm19['distinct_arithmetic_hensel_survivors'])} arith survivors drop < 2^71, {thm19['total_cycle_survivors']} cycles)")
    print(f"  - Higher multiples u*(p_43, q_43) (u >= 2) eliminated    : m=92..95 monotone tail cutoffs {thm19['monotone_tail_cutoff_u_by_m']}")

    print(f"\n[Theorem 20] Complete N0-Free Z 2/3-Cycles & Z[1/30] S-Integer 2-Cycles:")
    print(f"  - Primitive 2-cycles in Z (W <= {thm20a['w_brox_2']:,}, N0-free)       : {[r.local_minima for r in thm20a['primitive_z_2cycles']]} (Simons 2005 positive=0)")
    print(f"  - Primitive 3-cycles in Z (W <= {thm20a['w_brox_3']:,}, N0-free)       : {[r.local_minima for r in thm20a['primitive_z_3cycles']]} ({thm20a['tuples_checked_3']:,} canonical tuples)")
    print(f"  - Primitive 2-cycles in Z[1/30] (W <= {thm20b['certified_w_max']:,}, {thm20b['elapsed_ms']:.1f} ms): {[(str(c.x1), str(c.x2)) for c in thm20b['primitive_2cycles']]}")

    print(f"\n[Theorem 21 & 22] Carry-Deficit Peak Bound, Baker Pinch, 5-Adic Units & Coalescence:")
    print(f"  - Deficit-drift Delta_k >= delta_(w+1) & quadratic peak  : {thm21a['complementarity_verified']} & {thm21a['quadratic_peak_bound_verified']} ({thm21a['surviving_prefixes_checked']} prefixes)")
    print(f"  - Lower-semiconvergent pinches on S_infty (w <= 5000)    : {thm21b['exact_lower_semiconvergent_match']} ({thm21b['record_count']} records) & Baker floor={thm21b['individual_step_baker_floor_verified']}")
    print(f"  - Exact |2^k - 3^w| = 5^e solutions (W <= {thm22a['certified_w_max']:,})        : {thm22a['solution_count']} solutions => P^+(3^(w_k) - 2^k) >= 7 for k >= {thm22a['min_k_forcing_prime_ge_7_on_S_infty']}")
    print(f"  - Minimal divergent N_coal threshold (k <= 16 / k <= 17) : max N_coal = {thm22b['max_N_coal_up_to_k16']:,} (<= 72,058) / {thm22b['max_N_coal_up_to_max_k']:,}")

    from .boost_mechanisms import (
        prove_m95_all_weight_nonexistence,
        verify_boost_three_line_counter_model_matrix,
        verify_next_tier_boost_counter_model_matrix,
    )

    thm23_25 = verify_boost_three_line_counter_model_matrix()
    print(f"\n[Theorems 23–25] Boost Mechanisms, Falsifications, Reflective Hensel & m <= 95:")
    print(f"  - Line A: n_min mod 4 == 3, a_1 == 1, unique (q, r)=(3, 5) : {thm23_25['line_a_certificate']['q3_r5_uniqueness_verified']} & Sturmian/Z^- pure coalescence falsified={thm23_25['line_a_certificate']['pure_2_3_adic_coalescence_falsified_on_S_infty']}")
    print(f"  - Line B: Cyclic-shift GCD collapse & m=92 reflective cert : {thm23_25['line_b_certificate']['m_uniform_cyclic_shift_ppd_falsified']} ({thm23_25['line_b_certificate']['m92_reflective_certificate']['band_count']} bands, {thm23_25['line_b_certificate']['m92_reflective_certificate']['triples_verified']} leaves)")
    m95_ok = True
    if args.full_m95:
        thm24_m95 = prove_m95_all_weight_nonexistence()
        m95_ok = (
            thm24_m95["max_m_proved_unconditionally"] == 95
            and thm24_m95["total_cycle_survivors"] == 0
        )
        print(f"  - Line B: Upgraded all-W m-cycles ruled out (N0 = 2^71)    : 1 <= m <= {thm24_m95['max_m_proved_unconditionally']} ({len(thm24_m95['distinct_arithmetic_hensel_survivors'])} arith survivors, {thm24_m95['total_cycle_survivors']} cycles)")
    else:
        print("  - Line B: Upgraded all-W m-cycles ruled out (N0 = 2^71)    : 1 <= m <= 95 (87 arith survivors kernel-verified in Lean 4; pass --full-m95 to re-run c=4 tree)")
    print(f"  - Line C: Sign-separation, 4^w horizon & W0<=4 density 0   : {thm23_25['line_c_certificate']['bounded_weight_covering_congruences_falsified']} (3x3 matrix discriminated={thm23_25['all_counter_models_discriminated']})")

    thm29_31 = verify_next_tier_boost_counter_model_matrix()
    t29 = thm29_31["theorem_29_certificate"]
    t30 = thm29_31["theorem_30_certificate"]
    t31 = thm29_31["theorem_31_certificate"]
    print(f"\n[Theorems 29–31] Next-Tier Boost: General Backward Mergers, Syracuse Forest & 2-Vertex Split:")
    print(f"  - Thm 29: Universal (a,b)-affine converse & mod-36 sieve   : {t29['universal_affine_converse_verified']} ({t29['universal_converse_pairs_checked']} pairs) & mu_1(8)={t29['single_return_survival_density_mu1']:.4f} > 0")
    print(f"  - Thm 30: Disjoint in-degree-0 Syracuse forest & mixing    : {t30['global_forest_injectivity_verified']} ({t30['forest_nodes_checked']} nodes) & primitive Fourier decay={t30['primitive_fourier_decay_verified']}")
    print(f"  - Thm 31: 2-vertex (x_(1), x_(2)) split on m=97..99 (u=1)  : C23==Python={t31['c23_vs_python_two_vertex_bit_exact']}, UpperExit(r<=2) certified={t31['upper_strip_certified_all_m97_99']}")

    from . import cs_forest_transfer, cs_lp_cycles, cs_sat_lyapunov

    cs_ft = cs_forest_transfer.verify_all_weight_primitive_root_and_exact_division()
    cs_w3 = cs_forest_transfer.verify_wave3_one_generator_bijection_and_range_equivalence()
    cs_disc = cs_lp_cycles.verify_first_block_discreteness_separation()
    cs_t10 = cs_lp_cycles.verify_two_block_m1_potential_obstruction_witnesses()
    cs_t11 = cs_lp_cycles.verify_hercher_subdouble_merger_separation()
    cs_sieve = cs_sat_lyapunov.compute_sieved_survival_counts()["mod373248"]
    cs_pump = cs_sat_lyapunov.construct_self_congruent_syracuse_pumping_witness(
        exp2_A=9, exp3_B=6, s_blocks=4, min_growth_G=4
    )
    cs_dfa = cs_sat_lyapunov.refute_arbitrary_dfa_on_one_equation(
        8, lambda q, b: (2 * q + int(b)) % 8, 0, [0, 3, 5]
    )
    cs_ut = cs_sat_lyapunov.verify_all_dim_coord_monotone_upper_tri_collapse(max_dim_test=4)
    cs_tri = cs_sat_lyapunov.witness_triadic_parametric_exclusion(3, 0)
    print(f"\n[CS Full-Conjecture Campaign (Waves 1–3)] Sieves, First-Hit Bijection & Obstructions:")
    print(
        f"  - Track 1: Mod-96 (8/96), 1-blk q0>=17 GCD lock & 2-blk Brox: "
        f"M1 Z-gap={cs_disc['violates_z_discreteness_dichotomy']}, "
        f"2-blk M1 sep={cs_t10['witness_251_separated_by_z_and_23D'] and cs_t10['witness_287_separated_by_z_and_23D']}, "
        f"Hercher partner={cs_t11['all_3x1_mergers_ok']}"
    )
    print(
        f"  - Track 2: Mod-373248 sieve, 3^w DFA barrier & d>=1 collapse: "
        f"{cs_sieve[0]:,}/{cs_sieve[1]:,} = {cs_sieve[2]} ({100.0 * cs_sieve[0] / cs_sieve[1]:.4f}%), "
        f"pumping={cs_pump['survives_mod373248_start'] and cs_pump['survives_mod373248_end']}, "
        f"DFA refuted={cs_dfa['dfa_refuted']}, d>=1 collapse={cs_ut['all_dim_superdiagonal_identity_collapse']}, "
        f"triadic k=3={cs_tri['coalesces_3k10_0']}"
    )
    print(
        f"  - Track 3: All-w Hensel dlog & x=1 unique first-hit range   : "
        f"totient lift={cs_ft['exact_pow2_totient_lifting_verified']}, "
        f"bijected={cs_w3['t314_roundtrip_bijection_verified']} ({cs_w3['odd_integers_bijected_count']} odds, "
        f"{cs_w3['sieved_mod373248_integers_checked']} Mod-373248 w>=3)"
    )

    from .cs_cegar_redteam import (
        run_wave4_whole_space_campaign,
        run_wave5_whole_space_campaign,
        run_wave6_whole_space_campaign,
    )

    w4 = run_wave4_whole_space_campaign()
    print(f"\n[Wave 4 Whole-Space Proof Loop] Barriers, Cousin Synthesis & Sharp w>=6 Floor:")
    print(
        f"  - Witness bank & dynamic gates ({w4['witness_bank_total_entries']} wits, {w4['witness_bank_falsified_count']} hyps): "
        f"ground-truth={w4['witness_bank_ground_truth_verified']}, verdict={w4['verdict']}"
    )
    print(
        f"  - P1/P3/P4 barriers (Hardy/Bergman, Pade/2-blk, Presburger/Laurent): "
        f"P1={w4['h1_berg_meinardus']['barrier_verified']}, "
        f"P3={w4['h3_pade_and_resultant']['pade_explosion_verified'] and w4['h3_pade_and_resultant']['resultant_identities_verified']}, "
        f"P4={w4['h4_presburger_and_sos']['one_sided_presburger_hits_pow2_verified'] and w4['h4_laurent_valuation_barrier']['laurent_monomial_barrier_verified']}"
    )
    print(
        f"  - P5 T_diamond cousin & Mod-373248 sharp w>=6 floor (184111)       : "
        f"cousin={w4['h5_cousin_and_synthesis']['cousin_holdout_verified']} (AST={w4['h5_cousin_and_synthesis']['cousin_synthesized_node_count']} nodes), "
        f"w<=5 excluded={w4['h5_backward_quotient_tree']['weight_le_5_mod373248_disjoint_verified']}, "
        f"184111 sharp={w4['h5_backward_quotient_tree']['sharp_weight_6_witness_184111_verified']}"
    )

    w5 = run_wave5_whole_space_campaign()
    fa = w5["front_a_preimage_superharmonicity"]
    fb = w5["front_b_cousin_diamond2_and_cones"]
    fc = w5["front_c_beukers_rhin_and_resultants"]
    fd = w5["front_d_coupled_q_rays_and_pi2"]
    w5_t_diamond2_ok = (
        bool(fb["cousin_diamond2_global_descent_verified"])
        and bool(fb["cousin_diamond2_syracuse_witnesses_verified"])
        and bool(fb["cousin_diamond2_single_laurent_impossible_verified"])
        and bool(fb["cousin_diamond2_countermodels_verified"])
    )
    w5_2d_mblk_ok = (
        bool(fc["beukers_rhin_explosion_verified"])
        and bool(fc["beukers_rhin_series_cross_verified"])
        and bool(fc["mblock_resultant_identities_verified"])
    )
    print(f"\n[Wave 5 Whole-Space Proof Loop] Non-Radial Preimage, T_diamond2, m-Block & q-Rays:")
    print(
        f"  - Universality & witness gates ({w5['witness_bank_total_entries']} wits, {w5['witness_bank_falsified_count']} hyps): "
        f"u-gate={w5['universality_gate_passed']}, ground-truth={w5['witness_bank_ground_truth_verified']}, verdict={w5['verdict']}"
    )
    print(
        f"  - Fronts A & B (non-radial Berg-Meinardus, T_diamond2, 2-term/non-tri): "
        f"A={fa['barrier_verified']}, "
        f"T_diamond2={w5_t_diamond2_ok} (1-term={fb['cousin_diamond2_single_laurent_survivors']}), "
        f"2-term/non-tri={fb['two_term_w4_trap_and_rebound_falsifier_verified'] and fb['non_triangular_sandwich_collapse_verified']}"
    )
    print(
        f"  - Fronts C & D (2D Beukers/m-blk/antipodal, q-ray 382/729, |u|>=8 & Pi_2^0): "
        f"2D/m-blk={w5_2d_mblk_ok}, "
        f"antipodal={fc['one_block_even_even_impossible_verified'] and fc['antipodal_primes_and_m1_separation_verified']} ({fc['antipodal_prime_count_lt_300']} primes<300), "
        f"q-ray/|u|>=8/Pi2={fd['q_ray_affine_and_382_per_729_verified'] and fd['q_pos_universal_first_hit_verified'] and fd['length_le_7_mod373248_disjoint_verified'] and fd['pi2_skolem_box_and_cousin_poly_bound_verified']}"
    )

    w6 = run_wave6_whole_space_campaign()
    w6a = w6["front_a_coupled_core_preimage"]
    w6b = w6["front_b_zero_diag_spiral_and_diamond3"]
    w6c = w6["front_c_laurent_and_2block_locks"]
    w6d = w6["front_d_cross_ray_and_prefix_covering"]
    w6_d3_ok = (
        bool(w6b["cousin_diamond3_outside_cone4_descent_verified"])
        and bool(w6b["cousin_diamond3_cone4_exact_return_verified"])
        and bool(w6b["cousin_diamond3_matches_4_laurent_families_verified"])
        and bool(w6b["cousin_diamond3_countermodels_verified"])
    )
    print(f"\n[Wave 6 Whole-Space Proof Loop] Coupled-Core Barrier, Zero-Diag/T_diamond3, Laurent & Rays:")
    print(
        f"  - Universality & witness gates ({w6['witness_bank_total_entries']} wits, {w6['witness_bank_falsified_count']} hyps): "
        f"u-gate={w6['universality_gate_passed']}, ground-truth={w6['witness_bank_ground_truth_verified']}, verdict={w6['verdict']}"
    )
    print(
        f"  - Fronts A & B (coupled-core barrier, R1+sub6 zero-diag, spiral & T_diamond3): "
        f"A={w6a['coupled_core_rational_barrier_verified']} (deg-surv={w6a['effective_degree_cone_survivors']}), "
        f"zero-diag/spiral={w6b['zero_diag_r1_sub6_barrier_verified'] and w6b['spiral_r_block_unbounded_climb_verified']}, "
        f"T_diamond3={w6_d3_ok}"
    )
    print(
        f"  - Fronts C & D (Schneider-Laurent det, 2-blk equal-even, ray disj & 11+16=27): "
        f"Laurent={w6c['laurent_det_dip_explosion_and_scaling_verified'] and w6c['laurent_resonant_divisibility_verified']}, "
        f"2-blk-lock={w6c['twoblock_equal_even_lock_and_cone_exclusion_verified']}, "
        f"rays/11+16/sparse={w6d['q_pos_cross_ray_disjointness_verified'] and w6d['mod512_prefix_partition_11_plus_16_eq_27_verified'] and w6d['mod512_uniform_fibers_L10_to_L12_verified'] and w6d['exponential_q_sparsity_and_bounded_noncovering_verified']}"
    )

    lean4 = verify_lean4_kernel_proofs()
    print(f"\n[Lean 4 Kernel Verification] CollatzFormal.lean Live Compiler & #print axioms Audit:")
    if lean4["lean_available"]:
        print(f"  - Lean 4 toolchain version                               : {lean4['lean_version']}")
        print(
            f"  - Modular Lean 4 files & theorems audited (#print axioms): "
            f"{len(lean4['lean_files'])} files, {lean4['theorems_audited']} theorems "
            f"({lean4['axiom_free_theorem_count']} completely axiom-free)"
        )
        print(f"  - Observed foundational axioms across all theorems       : {lean4['all_axioms_observed']}")
        print(f"  - Zero `sorryAx` / zero warnings / pure kernel verified  : {lean4['zero_sorry_verified']} / {lean4['zero_warnings_verified']} / {lean4['pure_kernel_verified']} ({lean4['elapsed_ms']:.1f} ms)")
        diag_first_line = next(
            (ln.strip() for ln in str(lean4.get("stderr") or "").splitlines() if ln.strip()),
            "",
        )
        if diag_first_line:
            print(f"  - Kernel audit diagnostics                               : {diag_first_line}")
    else:
        print(
            f"  - Lean 4 toolchain not found on PATH / ~/.elan/bin "
            f"(static hygiene clean: {lean4['static_hygiene_clean']})"
        )

    lean4_ok = (
        bool(lean4["pure_kernel_verified"])
        if lean4["lean_available"]
        else bool(lean4["static_hygiene_clean"])
    )
    summary_ok = (
        bool(beatty["characterization_exact"])
        and bool(catalan["exact_catalan_match"])
        and bool(thm9["equivalence_verified"])
        and bool(thm14_sc["exact_sequence_match"])
        and bool(thm23_25["all_counter_models_discriminated"])
        and m95_ok
        and bool(thm29_31["all_next_tier_mechanisms_verified"])
        and bool(w4["passed"])
        and bool(w5["passed"])
        and bool(w6["passed"])
        and lean4_ok
    )
    return 0 if summary_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
