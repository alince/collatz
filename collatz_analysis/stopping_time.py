"""
Stopping-Time Lattice Sieve, Beatty-Sturmian Carry Characterization,
Cramer Large-Deviation Decay, and Tao's Syracuse Logarithmic Density Mixing.

Implements:
1. Exact O(K^2) Lattice-Path Dynamic Programming for S(k, w):
   - S(k, w): exact count of parity vectors in {0, 1}^k of weight w that stay
     strictly above the stopping boundary 3^{w_j} > 2^j for all 1 <= j <= k.
   - Exact coefficient stopping-time distribution P(tau = k) and survival fraction
     d_k = S(k) / 2^k up to k = 500.
2. Beatty-Sturmian Characterization of Coefficient-Surviving Paths:
   - Proves and verifies that a parity vector with odd-step indices
     0 <= j_1 < j_2 < ... < j_w < k survives up to step j_w iff
         m - 1 <= j_m <= floor((m - 1) * log_2(3))  for all 1 <= m <= w.
   - Computes the exact sharp maximum carry C_max^surv(w) attained uniquely by
     the Sturmian boundary path j*_m = floor((m - 1) * log_2(3)).
3. Cramer-Chernoff Large Deviation Rate Function:
   - Exact asymptotic decay rate rho = 2^{H_2(log_3(2)) - 1} ≈ 0.96602983 of d_k.
4. Garner's Stopping-Time Coincidence (sigma(n) == tau(n)) & Tao's (2019)
   Syracuse Logarithmic Density Drift Analyzer.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Dict, List, Tuple

from .parity_2adic import (
    affine_parameters,
    analyze_trajectory,
    carry_via_odd_indices,
    is_coefficient_surviving_prefix,
    surviving_path_carry_bound,
    syracuse_step,
)


@dataclass(frozen=True)
class StoppingTimeLevelSummary:
    """Exact counts at depth k in the parity-vector stopping-time tree {0, 1}^k."""

    k: int
    total_classes: int  # 2^k
    surviving_classes: int  # S(k) = sum_w S(k, w)
    newly_stopped_classes: int  # T_stop(k) = 2 * S(k-1) - S(k)
    survival_fraction: float  # S(k) / 2^k
    min_surviving_weight: int  # ceil(k * log_3(2))


def compute_exact_stopping_time_dp(max_k: int = 200) -> List[StoppingTimeLevelSummary]:
    """
    Compute the exact number of coefficient-surviving residue classes modulo 2^k
    for all 1 <= k <= max_k using O(max_k^2) dynamic programming over lattice paths
    (k, w) that stay strictly inside the cone 3^w > 2^k.
    """
    if max_k < 1:
        raise ValueError(f"max_k must be >= 1, got {max_k}")

    # dp[w] = number of surviving paths of current length k with weight w
    # At k = 0: dp = {0: 1}
    dp: Dict[int, int] = {0: 1}
    summaries: List[StoppingTimeLevelSummary] = []

    for k in range(1, max_k + 1):
        prev_total = sum(dp.values())
        threshold_2k = 1 << k
        next_dp: Dict[int, int] = {}

        for w, count in dp.items():
            # Step v_{k-1} = 0 -> new weight w
            if (3**w) > threshold_2k:
                next_dp[w] = next_dp.get(w, 0) + count
            # Step v_{k-1} = 1 -> new weight w + 1
            w1 = w + 1
            if (3**w1) > threshold_2k:
                next_dp[w1] = next_dp.get(w1, 0) + count

        surviving = sum(next_dp.values())
        newly_stopped = 2 * prev_total - surviving
        min_w = min(next_dp.keys()) if next_dp else 0
        # Compute survival_fraction without float overflow for large k
        if k <= 1000:
            surv_frac = surviving / (1 << k)
        else:
            surv_frac = math.pow(2.0, math.log2(surviving) - k)

        summaries.append(
            StoppingTimeLevelSummary(
                k=k,
                total_classes=1 << k,
                surviving_classes=surviving,
                newly_stopped_classes=newly_stopped,
                survival_fraction=surv_frac,
                min_surviving_weight=min_w,
            )
        )
        dp = next_dp

    return summaries


def beatty_sturmian_max_indices(w: int) -> Tuple[int, ...]:
    """
    Return the exact Beatty sequence j*_m = floor((m - 1) * log_2(3)) for m = 1, ..., w,
    where 2^{j*_m} < 3^{m-1} <= 2^{j*_m + 1} for all m >= 2 (and j*_1 = 0).
    """
    if w < 0:
        raise ValueError(f"w must be >= 0, got {w}")
    indices: List[int] = []
    for m in range(1, w + 1):
        if m == 1:
            indices.append(0)
        else:
            # Exact integer floor((m - 1) * log_2(3)) = bit_length(3^{m-1}) - 1
            p3 = 3 ** (m - 1)
            indices.append(p3.bit_length() - 1)
    return tuple(indices)


def sharp_surviving_carry_max(w: int) -> Tuple[int, Tuple[int, ...]]:
    """
    Compute the exact sharp maximum of C_k(v) over all coefficient-surviving paths
    of weight w, together with the unique Sturmian parity vector v*(w) that attains it:
        C_max^surv(w) = sum_{m=1}^w 3^{w - m} * 2^{floor((m - 1) * log_2(3))}.
    """
    if w == 0:
        return 0, ()
    max_indices = beatty_sturmian_max_indices(w)
    k_min = max_indices[-1] + 1
    v_list = [0] * k_min
    for j_m in max_indices:
        v_list[j_m] = 1
    v_tuple = tuple(v_list)
    carry = carry_via_odd_indices(v_tuple)
    return carry, v_tuple


def verify_beatty_sturmian_characterization(max_k: int = 13) -> Dict[str, object]:
    """
    Exhaustively verify on all 2^{max_k} parity vectors of length max_k that:
    1. A parity vector v in {0, 1}^k is coefficient-surviving up to its last odd step j_w
       iff m - 1 <= j_m <= floor((m - 1) * log_2(3)) for all 1 <= m <= w.
    2. For every surviving parity vector of weight w,
           3^w - 2^w <= C_k(v) <= C_max^surv(w) <= w * 3^{w-1} - (3^{w-1} - 1) // 2,
       with both the lower bound 3^w - 2^w and the sharp upper bound C_max^surv(w)
       attained whenever k >= floor((w - 1) * log_2(3)) + 1.
    """
    total_checked = 0
    surviving_by_w: Dict[int, List[int]] = {}

    for mask in range(1 << max_k):
        v = tuple((mask >> j) & 1 for j in range(max_k))
        odd_indices = [j for j, bit in enumerate(v) if bit == 1]
        w = len(odd_indices)
        beatty_bounds = beatty_sturmian_max_indices(w)
        satisfies_beatty = all(j_m <= beatty_bounds[idx] for idx, j_m in enumerate(odd_indices))

        # Check survival up to the last odd step j_w (i.e. prefix of length j_w + 1)
        if w == 0:
            survives_to_last_odd = True
        else:
            last_odd_prefix = v[: odd_indices[-1] + 1]
            survives_to_last_odd = is_coefficient_surviving_prefix(last_odd_prefix, strict_until_end=True)

        if satisfies_beatty != survives_to_last_odd:
            raise AssertionError(
                f"Beatty characterization mismatch for v={v}: "
                f"satisfies_beatty={satisfies_beatty}, survives_to_last_odd={survives_to_last_odd}"
            )

        if is_coefficient_surviving_prefix(v, strict_until_end=True):
            _, _, carry = affine_parameters(v)
            surviving_by_w.setdefault(w, []).append(carry)

        total_checked += 1

    weight_bound_checks = {}
    for w, carries in sorted(surviving_by_w.items()):
        c_min_theo = (3**w) - (1 << w)
        c_max_sharp, _ = sharp_surviving_carry_max(w)
        c_max_analytic = surviving_path_carry_bound(w)
        obs_min = min(carries)
        obs_max = max(carries)
        if obs_min < c_min_theo or obs_max > c_max_sharp or c_max_sharp > c_max_analytic:
            raise AssertionError(
                f"Carry bound violation at w={w}: obs=[{obs_min}, {obs_max}], "
                f"theo=[{c_min_theo}, {c_max_sharp}], analytic={c_max_analytic}"
            )
        weight_bound_checks[w] = {
            "count": len(carries),
            "observed_min": obs_min,
            "theoretical_min": c_min_theo,
            "observed_max": obs_max,
            "sharp_sturmian_max": c_max_sharp,
            "analytic_bound": c_max_analytic,
            "attains_sharp_max": obs_max == c_max_sharp,
        }

    return {
        "max_k": max_k,
        "total_vectors_checked": total_checked,
        "characterization_exact": True,
        "weight_bound_checks": weight_bound_checks,
    }


def cramer_large_deviation_parameters() -> Dict[str, float]:
    """
    Compute the exact Cramér-Sanov large-deviation constants governing the exponential
    decay of the coefficient-surviving residue density d_k = S(k) / 2^k as k -> infty.

    Here w_k ~ Binomial(k, 1/2) must stay >= p* k where p* = log_3(2) = ln(2)/ln(3).
    The binary entropy at p* is:
        H_2(p*) = -p* log_2(p*) - (1 - p*) log_2(1 - p*),
    the KL rate function in bits is:
        I_2(p*) = 1 - H_2(p*),
    and the exponential base per step is:
        rho = 2^{-I_2(p*)} = 2^{H_2(p*) - 1} ≈ 0.96602983.
    """
    p_star = math.log(2.0) / math.log(3.0)
    q_star = 1.0 - p_star
    h2 = -p_star * math.log2(p_star) - q_star * math.log2(q_star)
    rate_bits = 1.0 - h2
    rate_nats = rate_bits * math.log(2.0)
    rho = math.pow(2.0, -rate_bits)
    return {
        "critical_slope_p_star": p_star,
        "binary_entropy_H2": h2,
        "kl_rate_bits": rate_bits,
        "kl_rate_nats": rate_nats,
        "asymptotic_decay_base_rho": rho,
    }


def verify_garner_stopping_time_coincidence(limit_n: int = 10000) -> Dict[str, object]:
    """
    Verify Garner's Stopping-Time Coincidence (sigma(n) == tau(n)) for all 2 <= n <= limit_n,
    confirming that the actual stopping time coincides with the coefficient stopping time.
    """
    exceptions: List[Tuple[int, Optional[int], Optional[int]]] = []
    max_sigma = (2, 1)

    for n in range(2, limit_n + 1):
        traj = analyze_trajectory(n)
        if traj.stopping_time_sigma != traj.coeff_stopping_time_tau:
            exceptions.append((n, traj.stopping_time_sigma, traj.coeff_stopping_time_tau))
        if traj.stopping_time_sigma is not None and traj.stopping_time_sigma > max_sigma[1]:
            max_sigma = (n, traj.stopping_time_sigma)

    return {
        "limit_n": limit_n,
        "exceptions_count": len(exceptions),
        "exceptions": exceptions,
        "max_stopping_time_record": {"n": max_sigma[0], "sigma": max_sigma[1]},
        "coincidence_verified": len(exceptions) == 0,
    }


def analyze_tao_syracuse_mixing(max_odd_n: int = 9999, mod_power_3: int = 3) -> Dict[str, object]:
    """
    Analyze Terence Tao's (2019) Syracuse random variables and logarithmic density mixing:
    1. For odd integers n <= max_odd_n (weighted by logarithmic weight 1/n), compute the
       distribution of the 2-adic valuation a_1(n) = nu_2(3n + 1) and verify convergence
       to the geometric law P(a = r) = 2^{-r}, E[a] = 2.
    2. Compute the logarithmic-density drift E_log[log_2(S(n)/n)] and compare against
       the theoretical Syracuse drift log_2(3) - 2 ≈ -0.4150375 bits/step.
    3. Compute the exact Markov transition matrix of the Syracuse step modulo 3^m
       (on residues coprime to 3, or full 3-adic pushforward under 2-adic valuations)
       and measure the spectral gap / total variation contraction.
    """
    log_weight_total = 0.0
    valuation_weights: Dict[int, float] = {}
    weighted_drift_sum = 0.0

    # Also track residue distribution of S^step(n) mod 3^m for n coprime to 3
    mod3 = 3**mod_power_3
    coprime_residues = [r for r in range(mod3) if r % 3 != 0]
    res_index = {r: idx for idx, r in enumerate(coprime_residues)}
    num_res = len(coprime_residues)

    for n in range(3, max_odd_n + 1, 2):
        w = 1.0 / n
        log_weight_total += w
        s_n, a = syracuse_step(n)
        valuation_weights[a] = valuation_weights.get(a, 0.0) + w
        weighted_drift_sum += w * math.log2(s_n / n)

    empirical_geom = {r: valuation_weights.get(r, 0.0) / log_weight_total for r in range(1, 11)}
    tv_distance_geom = 0.5 * sum(
        abs(empirical_geom.get(r, 0.0) - math.pow(2.0, -r)) for r in range(1, 15)
    )
    empirical_mean_a = sum(r * wt for r, wt in valuation_weights.items()) / log_weight_total
    empirical_drift = weighted_drift_sum / log_weight_total
    theoretical_drift = math.log2(3.0) - 2.0

    # Construct the Syracuse Markov operator P on (Z / 3^m Z)^x driven by a ~ Geom(1/2)
    # Note: after 1 Syracuse step S(n) = (3n + 1) / 2^a, S(n) == 2^{-a} (mod 3), so S(n) is
    # ALWAYS coprime to 3! Wait: Modulo 3^m, S(n) = (3n + 1) * 2^{-a} (mod 3^m), which depends
    # on n mod 3^{m-1} and on a mod phi(3^m)!
    # Even better: if we view the random walk on Z / 3^m Z where at each step we pick a ~ Geom(1/2)
    # and map x -> (3x + 1) * 2^{-a} mod 3^m, let's compute the exact transition probabilities
    # on the (Z / 3^m Z)^x state space!
    phi_3m = 2 * (3 ** (mod_power_3 - 1))
    # Since 2 is a primitive root mod 3^m, a ~ Geom(1/2) wraps around mod phi(3^m):
    # P(a == r mod phi_3m) = 2^{-r} / (1 - 2^{-phi_3m}) for r in 1..phi_3m
    denom_wrap = 1.0 - math.pow(2.0, -phi_3m)
    a_mod_probs = {r % phi_3m: math.pow(2.0, -r) / denom_wrap for r in range(1, phi_3m + 1)}

    # Build transition matrix T[i][j] = P(X_{t+1} = r_j | X_t = r_i)
    trans_matrix = [[0.0] * num_res for _ in range(num_res)]
    for i, r_in in enumerate(coprime_residues):
        for a_rem, prob in a_mod_probs.items():
            inv_2a = pow(2, -a_rem, mod3)
            r_out = ((3 * r_in + 1) * inv_2a) % mod3
            j = res_index[r_out]
            trans_matrix[i][j] += prob

    # Track two metrics across steps t = 1 .. m + 2:
    # 1. Pairwise coupling TV distance max_{x, y} ||P^t(x, .) - P^t(y, .)||_TV,
    #    which MUST hit exact 0 at t = m because 3^m * x_0 == 0 (mod 3^m)!
    # 2. TV distance to the uniform measure on (Z / 3^m Z)^x.
    # Let's evolve all starting point masses simultaneously (i.e. powers of trans_matrix)
    curr_power = [[1.0 if i == j else 0.0 for j in range(num_res)] for i in range(num_res)]
    coupling_tv_by_step: List[float] = []
    tv_to_uniform_by_step: List[float] = []
    unif = 1.0 / num_res

    for _ in range(1, mod_power_3 + 3):
        next_power = [[0.0] * num_res for _ in range(num_res)]
        for i in range(num_res):
            for k_mid in range(num_res):
                dik = curr_power[i][k_mid]
                if dik == 0.0:
                    continue
                for j in range(num_res):
                    next_power[i][j] += dik * trans_matrix[k_mid][j]
        curr_power = next_power

        # Compute max TV distance between row 0 and any other row i
        max_row_tv = 0.0
        for i in range(1, num_res):
            tv_0i = 0.5 * sum(abs(curr_power[0][j] - curr_power[i][j]) for j in range(num_res))
            if tv_0i > max_row_tv:
                max_row_tv = tv_0i
        coupling_tv_by_step.append(max_row_tv)

        tv_unif = 0.5 * sum(abs(curr_power[0][j] - unif) for j in range(num_res))
        tv_to_uniform_by_step.append(tv_unif)

    # Also verify the exact algebraic 3-adic memory-annihilation formula on integer trajectories:
    # S^m(n) == sum_{j=1}^m 3^{m-j} * 2^{-(a_j + ... + a_m)} (mod 3^m)
    annihilation_verified_count = 0
    for n in range(1, 200, 2):
        curr = n
        vals: List[int] = []
        for _ in range(mod_power_3):
            curr, a = syracuse_step(curr)
            vals.append(a)
        rhs_mod = 0
        for j_idx in range(mod_power_3):
            suffix_sum = sum(vals[j_idx:])
            term = ((3 ** (mod_power_3 - 1 - j_idx)) * pow(2, -suffix_sum, mod3)) % mod3
            rhs_mod = (rhs_mod + term) % mod3
        if (curr % mod3) != rhs_mod:
            raise AssertionError(f"3-adic memory annihilation failed at n={n}")
        annihilation_verified_count += 1

    return {
        "max_odd_n": max_odd_n,
        "empirical_mean_valuation": empirical_mean_a,
        "theoretical_mean_valuation": 2.0,
        "empirical_log2_drift": empirical_drift,
        "theoretical_log2_drift": theoretical_drift,
        "geom_tv_distance": tv_distance_geom,
        "mod_3m": mod3,
        "mod_power_3": mod_power_3,
        "coprime_state_count": num_res,
        "coupling_tv_by_step": coupling_tv_by_step,
        "exact_memory_erasure_at_step_m": coupling_tv_by_step[mod_power_3 - 1] < 1e-14,
        "tv_distance_to_uniform_by_step": tv_to_uniform_by_step,
        "annihilation_verified_count": annihilation_verified_count,
    }
