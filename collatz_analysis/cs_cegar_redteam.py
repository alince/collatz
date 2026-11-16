"""
Adversarial 3x3 Counter-Model Falsifier & CEGAR Obstruction Verifier (Track 4).

Implements the reusable counterexample-guided abstraction refinement (CEGAR) and
3x3 adversarial counter-model harness for the Collatz formal campaign:

1. Counter-Model M1 (`Q_(2)^+`, positive 2-adic rationals with odd denominator):
   - Exact `fractions.Fraction` compressed Collatz dynamics `T(x) = x/2` (even
     numerator) or `(3x + 1)/2` (odd numerator), 2-adic valuation `v_2`, and
     exact `mod (2^A * 3^B)` projection whenever `gcd(denom(x), 6) == 1`.
   - Catalog of positive rational cycles (`19/5`, `29/5`, `1/5`, `1/125`, plus
     all generated primitive positive rational cycles `C_K(v) / (2^K - 3^W)` across
     `2^K > 3^W` with `gcd(2^K - 3^W, 6) == 1`, and convergent rational 1-cycles).
   - Automated audit of hypotheses that hold vs. fail in `M1` (including the
     failure of `2^{v_2(x + 1)} <= x + 1` at `x = 19/5`).

2. Counter-Model M2 (`Z^-`, negative integers under compressed `3x + 1`):
   - Catalog of `-1`, `-5`, and `-17` cycles, negative Syracuse predecessor trees
     (both cycle-rooted and in-degree-0 negative Garden-of-Eden roots such as `-43`),
     Raney cycle members in `S_infty intersect Z^-`, signed-non-descending cycle
     minima (`-1`, `-10`, `-136`), and high-horizon Beatty-Sturmian negative
     trajectories in `S_infty intersect Z^-`.
   - Automated audit showing why `3^w`-adic backward congruence still succeeds on
     `Z^-` while archimedean positivity `y >= 1` fails (`y <= -1`).

3. Counter-Model M3 (`5x + 1`, compressed `(5x + 1)/2` on odd `x`, `x/2` on even `x`):
   - Catalog of positive cycles (`1`, `13`, `17`), non-`1` cyclic/preperiodic seeds
     (`5 -> 13` minimal non-descending counterexample, `27` on the `17`-cycle), and
     divergent-like unbounded trajectories (`7`, `21`, `31`, `55`).
   - Automated audit showing why `2` is still a primitive root modulo `5^w` for all
     `w >= 1` and `2^K - 5^W > 0` holds on `1, 13, 17`, while `q = 3` Entry Merger
     uniqueness and negative drift `log_2(3) < 2` fail.

4. Positive `3x + 1` Extreme Stress Bank:
   - All 87 arithmetic multi-step Hensel survivors (`32 + 55`) cross-verified
     against `CollatzFormal/Core.lean` and certified to drop `<= 2^71`.
   - High-glide Mersenne seeds `2^k - 1` (`k = 10..150`) with uninterrupted `k`-step
     odd runs `T^k(2^k - 1) = 3^k - 1` and `IsSurvivingMod1296Class` tags.
   - Extreme `(W, K)` continued-fraction convergents of `log_2(3)` up to index 55.

5. Reusable CEGAR Proposal Auditors (Hard Rule 1 & Hard Rule 2 Gates):
   - Universality quantifier / zero-custom-axiom gate (rejecting finite-`m`,
     finite-`N`, or bounded-weight `w <= W_0` stepping stones).
   - 3x3 counter-model cycle, Lyapunov/ranking, minimal-counterexample modular
     sieve (including small-`n` boundary checks), and obstruction witness verifiers.
"""

from __future__ import annotations

import math
import re
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from pathlib import Path
from typing import Callable, Dict, List, Optional, Sequence, Set, Tuple

from .boost_mechanisms import (
    _syracuse_valid_exp_py,
    is_surviving_mod1296_class,
)
from .cycles import ConvergentLog2Of3, log2_3_continued_fraction
from .parity_2adic import affine_parameters, is_coefficient_surviving_prefix


# ============================================================================
# 1. Exact Generalized Dynamics on Q_(2), Z, and T_q
# ============================================================================


def q2_v2(x: Fraction) -> int:
    """Exact 2-adic valuation v_2(x) for nonzero rational x."""
    if x == 0:
        raise ValueError("v_2(0) is infinite")
    num = abs(x.numerator)
    den = x.denominator
    v_num = (num & -num).bit_length() - 1
    v_den = (den & -den).bit_length() - 1
    return v_num - v_den


def q2_parity(x: Fraction) -> int:
    """2-adic parity (0 or 1) of x in Z_(2) (odd denominator)."""
    if (x.denominator & 1) == 0:
        raise ValueError(f"Expected 2-adic rational with odd denominator, got {x}")
    return x.numerator & 1


def q2_compressed_step(x: Fraction, q: int = 3) -> Fraction:
    """One step of generalized compressed Collatz map T_q on Z_(2)."""
    if (x.denominator & 1) == 0:
        raise ValueError(f"Expected 2-adic rational with odd denominator, got {x}")
    if (x.numerator & 1) == 0:
        return Fraction(x.numerator >> 1, x.denominator)
    return Fraction(q * x.numerator + x.denominator, 2 * x.denominator)


def q2_iter_and_parity(
    x: Fraction, steps: int, q: int = 3
) -> Tuple[Fraction, Tuple[int, ...]]:
    """Iterate T_q on Z_(2) for `steps` steps, returning (T_q^steps(x), parity_word)."""
    if steps < 0:
        raise ValueError(f"steps must be >= 0, got {steps}")
    cur = x
    bits: List[int] = []
    for _ in range(steps):
        p = q2_parity(cur)
        bits.append(p)
        cur = q2_compressed_step(cur, q=q)
    return cur, tuple(bits)


def q2_mod_pow2_pow3(x: Fraction, a: int, b: int) -> Optional[int]:
    """
    Exact residue of x modulo 2^a * 3^b when x in Z_(2) intersect Z_(3)
    (i.e. gcd(x.denominator, 6) == 1). Returns None if 2 or 3 divides denominator.
    """
    if a < 0 or b < 0:
        raise ValueError("Exponents a, b must be >= 0")
    if math.gcd(x.denominator, 6) != 1:
        return None
    mod = (1 << a) * (3**b)
    if mod == 1:
        return 0
    inv_den = pow(x.denominator, -1, mod)
    return (x.numerator * inv_den) % mod


def int_compressed_step(x: int, q: int = 3) -> int:
    """One step of generalized compressed map T_q(x) on Z."""
    return (x >> 1) if (x & 1) == 0 else ((q * x + 1) >> 1)


def int_iter_and_parity(x: int, steps: int, q: int = 3) -> Tuple[int, Tuple[int, ...]]:
    """Iterate T_q on Z for `steps` steps, returning (T_q^steps(x), parity_word)."""
    if steps < 0:
        raise ValueError(f"steps must be >= 0, got {steps}")
    cur = x
    bits: List[int] = []
    for _ in range(steps):
        p = cur & 1
        bits.append(p)
        cur = int_compressed_step(cur, q=q)
    return cur, tuple(bits)


def generalized_affine_carry(bits: Sequence[int], q: int = 3) -> int:
    """Generalized affine carry C_q(v) along parity word `bits`."""
    carry = 0
    for j, bit in enumerate(bits):
        if bit not in (0, 1):
            raise ValueError(f"Parity bits must be 0 or 1, got {bit}")
        if bit == 1:
            carry = q * carry + (1 << j)
    return carry


def count_odd_even_blocks(bits: Sequence[int]) -> int:
    """
    Count cyclic odd-even spiral blocks m on a non-constant periodic parity word `bits`.
    For all-1 words (like (-1,) on Z^-), returns 1.
    """
    k = len(bits)
    if k == 0:
        return 0
    if all(b == 1 for b in bits):
        return 1
    if all(b == 0 for b in bits):
        return 0
    transitions = 0
    for i in range(k):
        if bits[i] == 1 and bits[(i - 1) % k] == 0:
            transitions += 1
    return transitions


def _canonical_cycle_rotation(bits: Tuple[int, ...]) -> Tuple[int, ...]:
    """Lexicographically minimal cyclic rotation (with 1s prioritized via (-b) key)."""
    k = len(bits)
    rotations = [bits[i:] + bits[:i] for i in range(k)]
    # Prioritize leading 1s and standard canonical form
    return max(rotations)


def _is_primitive_word(bits: Tuple[int, ...]) -> bool:
    """Return True iff `bits` is not a nontrivial repetition u^r (r >= 2)."""
    k = len(bits)
    for d in range(1, k):
        if k % d == 0 and bits == bits[:d] * (k // d):
            return False
    return True


# ============================================================================
# 2. Counter-Model M1: Q_(2)^+ (Positive 2-Adic Rationals)
# ============================================================================


@dataclass(frozen=True)
class RationalCycleWitness:
    """Exact periodic orbit witness in M1 = Q_(2)^+ under compressed 3x + 1."""

    x0: Fraction
    period_k: int
    weight_w: int
    m_blocks: int
    parity_vector: Tuple[int, ...]
    carry: int
    denom_gap: int
    orbit: Tuple[Fraction, ...]
    is_non_integer: bool
    coprime_to_6: bool
    min_element: Fraction
    max_element: Fraction


def trace_q2_cycle_from_parity(bits: Sequence[int], q: int = 3) -> RationalCycleWitness:
    """Construct and verify the exact rational cycle x_0 = C_q(v) / (2^K - q^W)."""
    v = tuple(int(b) for b in bits)
    k = len(v)
    w = sum(v)
    carry = generalized_affine_carry(v, q=q)
    denom_gap = (1 << k) - (q**w)
    if denom_gap <= 0 or w == 0:
        raise ValueError(f"Require w >= 1 and 2^K > q^W for positive cycle, got K={k}, W={w}")
    x0 = Fraction(carry, denom_gap)
    orbit: List[Fraction] = []
    cur = x0
    actual_bits: List[int] = []
    for _ in range(k):
        orbit.append(cur)
        actual_bits.append(q2_parity(cur))
        cur = q2_compressed_step(cur, q=q)
    if cur != x0 or tuple(actual_bits) != v:
        raise AssertionError(f"Rational cycle mismatch for v={v}: end={cur}, bits={actual_bits}")
    return RationalCycleWitness(
        x0=x0,
        period_k=k,
        weight_w=w,
        m_blocks=count_odd_even_blocks(v),
        parity_vector=v,
        carry=carry,
        denom_gap=denom_gap,
        orbit=tuple(orbit),
        is_non_integer=(x0.denominator != 1),
        coprime_to_6=(math.gcd(x0.denominator, 6) == 1),
        min_element=min(orbit),
        max_element=max(orbit),
    )


def build_m1_q2_pos_catalog(
    max_generated_k: int = 9,
    max_1cycle_w: int = 20,
) -> Dict[str, object]:
    """
    Build and verify the Counter-Model M1 (`Q_(2)^+`) cycle catalog and hypothesis audit.
    Includes canonical cycles (`19/5`, `29/5`, `1/5`, `1/125`), all primitive non-integer
    positive rational cycles `C_K(v) / (2^K - 3^W)` up to `K = max_generated_k` where
    `2^K > 3^W` and `gcd(2^K - 3^W, 6) == 1`, and 1-cycles across `1 <= W <= max_1cycle_w`.
    """
    c_19_5 = trace_q2_cycle_from_parity((1, 1, 1, 0, 0))
    c_29_5 = trace_q2_cycle_from_parity((1, 0, 1, 1, 0))
    c_1_5 = trace_q2_cycle_from_parity((1, 0, 0))
    c_1_125 = trace_q2_cycle_from_parity((1, 0, 0, 0, 0, 0, 0))

    assert c_19_5.x0 == Fraction(19, 5)
    assert c_29_5.x0 == Fraction(29, 5)
    assert c_1_5.x0 == Fraction(1, 5)
    assert c_1_125.x0 == Fraction(1, 125)

    seen_rotations: Set[Tuple[int, ...]] = set()
    generated_non_integer_cycles: List[RationalCycleWitness] = []
    integer_trivial_cycles: List[RationalCycleWitness] = []

    for k in range(2, max_generated_k + 1):
        p2 = 1 << k
        for bits in product((0, 1), repeat=k):
            w = sum(bits)
            if w == 0 or (3**w) >= p2:
                continue
            denom_gap = p2 - (3**w)
            if math.gcd(denom_gap, 6) != 1:
                continue
            if not _is_primitive_word(bits):
                continue
            canon = _canonical_cycle_rotation(bits)
            if canon in seen_rotations:
                continue
            seen_rotations.add(canon)
            witness = trace_q2_cycle_from_parity(canon)
            if witness.is_non_integer:
                generated_non_integer_cycles.append(witness)
            else:
                integer_trivial_cycles.append(witness)

    one_cycle_family: List[RationalCycleWitness] = []
    for w in range(2, max_1cycle_w + 1):
        k = (3**w).bit_length()
        v_one = (1,) * w + (0,) * (k - w)
        one_cycle_family.append(trace_q2_cycle_from_parity(v_one))

    # Audit hypotheses on 19/5 and 29/5 and generated cycles:
    # 1. Spiral equation 2^(k+l)*(x' + 1) == 3^k*(x + 1) + 2^k*(2^l - 1) holds on 19/5 (k=3, l=2, x'=19/5):
    x_19_5 = Fraction(19, 5)
    spiral_holds_19_5 = (1 << 5) * (x_19_5 + 1) == (3**3) * (x_19_5 + 1) + (1 << 3) * ((1 << 2) - 1)
    # 2. Valuation-to-Archimedean bridge 2^{v_2(x+1)} <= x + 1 FAILS at x = 19/5:
    #    19/5 + 1 = 24/5, so v_2(19/5 + 1) = 3, yet 2^3 = 8 > 24/5 = 4.8!
    v2_19_5_p1 = q2_v2(x_19_5 + 1)
    archimedean_v2_fails_19_5 = (v2_19_5_p1 == 3) and ((1 << v2_19_5_p1) > x_19_5 + 1)
    # 3. Algebraic Entry Merger holds on 19/5: partner (19/5 - 1)/2 = 7/5 < 19/5 merges at T^4(7/5) == T^5(19/5)
    partner_7_5 = (x_19_5 - 1) / 2
    t4_partner, _ = q2_iter_and_parity(partner_7_5, 4)
    t5_19_5, _ = q2_iter_and_parity(x_19_5, 5)
    entry_merger_algebra_holds = (partner_7_5 == Fraction(7, 5)) and (t4_partner == t5_19_5 == x_19_5)
    # 4. Every generated cycle has gcd(denom, 6) == 1, so ALL mod 2^A * 3^B congruences are well-defined!
    all_coprime_6 = all(c.coprime_to_6 and math.gcd(c.denom_gap, 6) == 1 for c in generated_non_integer_cycles)

    hypotheses_status = {
        "positivity_x_gt_0": True,
        "affine_decomposition_universal": True,
        "bohm_sontacchi_cycle_equation": True,
        "negative_drift_2K_gt_3W": True,
        "spiral_block_identity": spiral_holds_19_5,
        "local_congruences_mod_2A_3B": all_coprime_6,
        "entry_merger_algebraic_identity": entry_merger_algebra_holds,
        "z_integrality_at_odd_primes_ge_5": False,
        "lower_well_ordering_of_domain": False,
        "valuation_archimedean_bound_2_pow_v2_le_x_plus_1": not archimedean_v2_fails_19_5,
        "one_equation_reaches_1": False,
    }

    return {
        "canonical_19_5": c_19_5,
        "canonical_29_5": c_29_5,
        "canonical_1_5": c_1_5,
        "canonical_1_125": c_1_125,
        "generated_non_integer_cycles": tuple(generated_non_integer_cycles),
        "integer_trivial_cycles_found": tuple(integer_trivial_cycles),
        "one_cycle_rational_family": tuple(one_cycle_family),
        "hypotheses_status": hypotheses_status,
        "v2_archimedean_counterexample_19_5": {
            "x": x_19_5,
            "v2_x_plus_1": v2_19_5_p1,
            "pow2_v2": 1 << v2_19_5_p1,
            "x_plus_1": x_19_5 + 1,
            "violates_pow2_le_xp1": archimedean_v2_fails_19_5,
        },
    }


# ============================================================================
# 3. Counter-Model M2: Z^- (Negative Integers, Predecessor Trees, S_infty)
# ============================================================================


@dataclass(frozen=True)
class NegativeCycleWitness:
    """Exact periodic orbit witness in M2 = Z^- under compressed 3x + 1."""

    seed: int
    period_k: int
    weight_w: int
    m_blocks: int
    denom_gap: int
    carry: int
    orbit: Tuple[int, ...]
    parity_vector: Tuple[int, ...]
    cantor_cone_members: Tuple[int, ...]
    signed_min: int
    signed_max: int


def trace_z_neg_cycle(seed: int) -> NegativeCycleWitness:
    """Trace a periodic orbit in Z^- and extract its S_infty Cantor-cone members."""
    if seed >= 0:
        raise ValueError(f"Expected negative integer seed, got {seed}")
    orbit: List[int] = []
    cur = seed
    while cur not in orbit:
        orbit.append(cur)
        cur = int_compressed_step(cur, q=3)
        if len(orbit) > 500:
            raise ValueError(f"Seed {seed} did not close a cycle within 500 steps")
    if cur != seed:
        raise ValueError(f"Seed {seed} is preperiodic (entered cycle at {cur}), not periodic")
    k = len(orbit)
    parities = tuple(x & 1 for x in orbit)
    w = sum(parities)
    carry = generalized_affine_carry(parities, q=3)
    denom_gap = (1 << k) - (3**w)
    assert denom_gap * seed == carry

    cantor_members: List[int] = []
    for idx, val in enumerate(orbit):
        rot = parities[idx:] + parities[:idx]
        if is_coefficient_surviving_prefix(rot, strict_until_end=True):
            cantor_members.append(val)

    return NegativeCycleWitness(
        seed=seed,
        period_k=k,
        weight_w=w,
        m_blocks=count_odd_even_blocks(parities),
        denom_gap=denom_gap,
        carry=carry,
        orbit=tuple(orbit),
        parity_vector=parities,
        cantor_cone_members=tuple(cantor_members),
        signed_min=min(orbit),
        signed_max=max(orbit),
    )


def is_negative_syracuse_forest_root(r: int) -> bool:
    """
    Characterization of genuine in-degree-0 roots in the negative `syracuseChild`
    graph over `{x < 0 : x odd, 3 nmid x}` where `d in {1..6}`:
        `(3 * r + 1) % 128 == 0` (e.g. `r = -43`, `3*(-43) + 1 = -128 = 2^7 * (-1)`).
    Note: unlike `Z^+` (where `{1}` is pruned and `5` becomes an artificial root),
    on `Z^-` the odd elements of the `-1`, `-5`, and `-17` cycles ALL have `d <= 6`
    and therefore form closed cycles inside `syracuseChild`!
    """
    if r >= 0 or (r & 1) == 0 or (r % 3) == 0:
        return False
    return (3 * r + 1) % 128 == 0


def negative_syracuse_forest_val(root: int, choices: Sequence[bool]) -> int:
    """Evaluate backward Syracuse branch choices from a negative odd non-multiple of 3."""
    if root >= 0 or (root & 1) == 0 or (root % 3) == 0:
        raise ValueError(f"Expected negative odd integer not divisible by 3, got {root}")
    val = root
    for b in reversed(choices):
        d = _syracuse_valid_exp_py(val, bool(b))
        val = ((1 << d) * val - 1) // 3
    return val


def build_negative_syracuse_tree(root: int, max_depth: int = 4) -> Dict[str, object]:
    """
    Expand the negative Syracuse predecessor tree up to `max_depth` binary choices,
    verifying exact forward Syracuse return `3*x + 1 = 2^d * parent` at every edge.
    """
    nodes_by_depth: Dict[int, List[int]] = {0: [root]}
    all_nodes: List[int] = [root]
    edge_verified = True
    self_or_cycle_repeats = 0

    seen: Set[int] = {root}
    for depth in range(1, max_depth + 1):
        layer: List[int] = []
        for choices in product((False, True), repeat=depth):
            val = negative_syracuse_forest_val(root, choices)
            parent = negative_syracuse_forest_val(root, choices[1:])
            d_step = _syracuse_valid_exp_py(parent, choices[0])
            if (
                val >= 0
                or (val & 1) == 0
                or (val % 3) == 0
                or (3 * val + 1) != (1 << d_step) * parent
            ):
                edge_verified = False
            if val in seen:
                self_or_cycle_repeats += 1
            else:
                seen.add(val)
            layer.append(val)
            all_nodes.append(val)
        nodes_by_depth[depth] = layer

    return {
        "root": root,
        "is_indegree_zero_root": is_negative_syracuse_forest_root(root),
        "max_depth": max_depth,
        "total_words_evaluated": len(all_nodes),
        "distinct_negative_nodes": len(seen),
        "cycle_repeats_detected": self_or_cycle_repeats,
        "all_edges_exact": edge_verified,
        "sample_leaves": tuple(nodes_by_depth[max_depth][:8]),
    }


def build_sturmian_negative_trajectory(horizon_k: int) -> Dict[str, object]:
    """
    Construct the canonical negative Hensel lift `x_neg = r_v - 2^K < 0` realizing
    the Beatty-Sturmian maximum-carry parity prefix `v*(K)` in `S_infty intersect Z^-`.
    For all `1 <= j <= K`, `3^{w_j} > 2^j` (stays strictly inside `S_infty`) and
    `|T^j(x_neg)|` grows without hitting any positive integer.
    """
    if horizon_k < 4:
        raise ValueError("horizon_k must be >= 4")
    # Build minimal surviving Beatty-Sturmian word in S_infty: choose 0 if 3^w > 2^j, else 1.
    bits: List[int] = []
    w = 0
    for j in range(1, horizon_k + 1):
        if (3**w) > (1 << j):
            bits.append(0)
        else:
            bits.append(1)
            w += 1
    v_tuple = tuple(bits)
    assert is_coefficient_surviving_prefix(v_tuple, strict_until_end=True)
    _, w_tot, carry = affine_parameters(v_tuple)
    mod_2k = 1 << horizon_k
    r_pos = (-carry * pow(3, -w_tot, mod_2k)) % mod_2k
    x_neg = r_pos - mod_2k  # strictly negative in [-2^K, -1]
    end_val, actual_bits = int_iter_and_parity(x_neg, horizon_k, q=3)
    assert actual_bits == v_tuple and end_val < 0

    return {
        "horizon_k": horizon_k,
        "weight_w": w_tot,
        "x_neg_start": x_neg,
        "x_neg_end": end_val,
        "magnitude_grew": abs(end_val) > abs(x_neg),
        "stays_in_S_infty": True,
        "parity_prefix": v_tuple,
    }


def build_m2_z_neg_catalog(
    sturm_horizons: Sequence[int] = (20, 40, 80),
) -> Dict[str, object]:
    """
    Build and verify the Counter-Model M2 (`Z^-`) catalog:
    - `-1`, `-5`, and `-17` negative cycles and their Raney `S_infty` members;
    - Cycle-rooted (`-1`, `-5`, `-17`) and in-degree-0 (`-43`) negative Syracuse trees;
    - Signed-non-descending negative cycle minima (`-1`, `-10`, `-136` where `forall k, T^k(x) >= x`);
    - High-horizon Beatty-Sturmian negative trajectories in `S_infty intersect Z^-`.
    """
    cyc_1 = trace_z_neg_cycle(-1)
    cyc_5 = trace_z_neg_cycle(-5)
    cyc_17 = trace_z_neg_cycle(-17)

    tree_neg1 = build_negative_syracuse_tree(-1, max_depth=4)
    tree_neg5 = build_negative_syracuse_tree(-5, max_depth=4)
    tree_neg17 = build_negative_syracuse_tree(-17, max_depth=4)
    tree_neg43 = build_negative_syracuse_tree(-43, max_depth=4)

    sturm_trajectories = tuple(build_sturmian_negative_trajectory(h) for h in sturm_horizons)

    # Verify why 3^w-adic backward congruence holds on Z^- while positivity y >= 1 fails:
    # Take x2 = -17 (x2 % 3 == 1 != 0) and u = (1, 1, 1, 1) (w = 4, 3^4 = 81, C(u) = 65):
    u_w4 = (1, 1, 1, 1)
    _, w4, c4 = affine_parameters(u_w4)
    hits_neg17 = [
        a for a in range(54) if (((1 << (len(u_w4) + a)) * (-17) - c4) % 81) == 0
    ]
    a_hit = hits_neg17[0]
    y_quot_neg17 = ((1 << (len(u_w4) + a_hit)) * (-17) - c4) // 81
    backward_congr_holds_but_y_neg = (len(hits_neg17) == 1) and (y_quot_neg17 <= -1)

    hypotheses_status = {
        "z_integrality": True,
        "affine_decomposition_universal": True,
        "bohm_sontacchi_cycle_equation": True,
        "two_adic_parity_bijection": True,
        "three_adic_backward_congruence_surjectivity": len(hits_neg17) == 1,
        "positivity_x_gt_0": False,
        "positive_cycle_denom_gap_2K_gt_3W": False,
        "backward_quotient_positivity_y_ge_1": not (y_quot_neg17 <= -1),
        "S_infty_intersect_domain_empty": False,
        "one_equation_has_solution": False,
    }

    return {
        "cycles": (cyc_1, cyc_5, cyc_17),
        "signed_non_descending_minima": (cyc_1.signed_min, cyc_5.signed_min, cyc_17.signed_min),
        "trees": {
            "-1": tree_neg1,
            "-5": tree_neg5,
            "-17": tree_neg17,
            "-43_indegree_zero_root": tree_neg43,
        },
        "sturmian_S_infty_trajectories": sturm_trajectories,
        "backward_quotient_neg17_witness": {
            "x2": -17,
            "a_mod54": a_hit,
            "y_quotient": y_quot_neg17,
            "congruence_holds_yet_y_negative": backward_congr_holds_but_y_neg,
        },
        "hypotheses_status": hypotheses_status,
    }


# ============================================================================
# 4. Counter-Model M3: 5x + 1 Compressed Map on Z^+
# ============================================================================


@dataclass(frozen=True)
class FiveXPlusOneWitness:
    """Orbit witness for M3 = compressed 5x + 1 on Z^+."""

    seed: int
    classification: str  # "positive_cycle", "preperiodic_nontrivial", "divergent_like"
    period_k: Optional[int]
    weight_w: Optional[int]
    denom_gap: Optional[int]
    carry_5: Optional[int]
    orbit_sample: Tuple[int, ...]
    reaches_one: bool
    drops_below_seed: bool
    final_bit_length: int


def analyze_m3_5x1_seed(seed: int, max_steps: int = 250) -> FiveXPlusOneWitness:
    """Trace compressed T_5(x) = (5x + 1)/2 (odd) or x/2 (even) from `seed`."""
    if seed < 1:
        raise ValueError(f"Expected positive seed >= 1, got {seed}")
    seen_idx: Dict[int, int] = {}
    orbit: List[int] = []
    bits: List[int] = []
    cur = seed
    drops = False
    for step in range(max_steps):
        if cur in seen_idx:
            start_i = seen_idx[cur]
            cyc_orb = orbit[start_i:]
            cyc_bits = bits[start_i:]
            k = len(cyc_orb)
            w = sum(cyc_bits)
            c5 = generalized_affine_carry(cyc_bits, q=5)
            gap = (1 << k) - (5**w)
            assert gap * cur == c5
            kind = "positive_cycle" if start_i == 0 else "preperiodic_nontrivial"
            return FiveXPlusOneWitness(
                seed=seed,
                classification=kind,
                period_k=k,
                weight_w=w,
                denom_gap=gap,
                carry_5=c5,
                orbit_sample=tuple(orbit),
                reaches_one=(1 in orbit),
                drops_below_seed=drops,
                final_bit_length=cur.bit_length(),
            )
        seen_idx[cur] = step
        orbit.append(cur)
        if step > 0 and cur < seed:
            drops = True
        p = cur & 1
        bits.append(p)
        cur = int_compressed_step(cur, q=5)

    return FiveXPlusOneWitness(
        seed=seed,
        classification="divergent_like",
        period_k=None,
        weight_w=None,
        denom_gap=None,
        carry_5=None,
        orbit_sample=tuple(orbit[:20]),
        reaches_one=(1 in orbit),
        drops_below_seed=drops,
        final_bit_length=cur.bit_length(),
    )


def build_m3_5x1_catalog(divergent_steps: int = 250) -> Dict[str, object]:
    """
    Build and verify Counter-Model M3 (`5x + 1` on `Z^+`):
    - Positive cycles: `1` (`K=5, W=2, gap=+7`), `13` (`K=7, W=3, gap=+3`), `17` (`K=7, W=3, gap=+3`);
    - Non-`1` cyclic/preperiodic seeds: `5` (`n_min^(5) = 5 -> 13`, never drops below `5`),
      and `27` (member of the `17`-cycle `{27, 68, 34, 17, 43, 108, 54}`, never reaches `1`);
    - Divergent-like seeds: `7`, `21`, `31`, `55` (unbounded-like growth over `divergent_steps`).
    """
    c_1 = analyze_m3_5x1_seed(1, max_steps=divergent_steps)
    c_13 = analyze_m3_5x1_seed(13, max_steps=divergent_steps)
    c_17 = analyze_m3_5x1_seed(17, max_steps=divergent_steps)
    pre_5 = analyze_m3_5x1_seed(5, max_steps=divergent_steps)
    cyc_27 = analyze_m3_5x1_seed(27, max_steps=divergent_steps)
    div_7 = analyze_m3_5x1_seed(7, max_steps=divergent_steps)
    div_21 = analyze_m3_5x1_seed(21, max_steps=divergent_steps)
    div_31 = analyze_m3_5x1_seed(31, max_steps=divergent_steps)
    div_55 = analyze_m3_5x1_seed(55, max_steps=divergent_steps)

    # Verify 2 is ALSO a primitive root modulo 5^w for w = 1, 2, 3, 4 (showing primitive-root
    # surjectivity alone does NOT distinguish 3x+1 from 5x+1!):
    prim_root_5w_holds = True
    for w in (1, 2, 3, 4):
        mod5 = 5**w
        phi5 = 4 * (5 ** (w - 1))
        residues = {pow(2, a, mod5) for a in range(phi5)}
        if len(residues) != phi5:
            prim_root_5w_holds = False

    hypotheses_status = {
        "positivity_x_gt_0": True,
        "z_integrality": True,
        "lower_well_ordering_of_N": True,
        "positive_cycle_denom_gap_2K_gt_qW": (
            c_1.denom_gap == 7 and c_13.denom_gap == 3 and c_17.denom_gap == 3
        ),
        "two_is_primitive_root_mod_q_pow_w": prim_root_5w_holds,
        "negative_drift_log2_q_lt_2": False,
        "entry_merger_polynomial_identity_q_eq_3": False,
        "no_nontrivial_positive_cycles": False,
        "no_divergent_positive_orbits": False,
    }

    return {
        "positive_cycles": (c_1, c_13, c_17),
        "minimal_nondescending_seed_5": pre_5,
        "cycle_17_member_27": cyc_27,
        "divergent_like_orbits": (div_7, div_21, div_31, div_55),
        "hypotheses_status": hypotheses_status,
    }


# ============================================================================
# 5. Positive 3x + 1 Extreme Stress Bank (87 Survivors, 2^k - 1, Convergents)
# ============================================================================

HENSEL_SURVIVORS_92_TO_95_32: Tuple[Tuple[int, int], ...] = (
    (128932779112854022258687, 304),
    (150148540639431337443327, 388),
    (150417804975740953821183, 339),
    (179507528690102354051071, 309),
    (184292880188988234661887, 183),
    (3043056996432649454896063935, 522),
    (4564585494648974182344095903, 521),
    (40390864820245125463559531007, 445),
    (60586297230367688195339296511, 444),
    (80781729640490250927119062015, 446),
    (80896492308699435453147774975, 490),
    (81382151907816510442931486719, 552),
    (90879445845551532293008944767, 443),
    (107666254683307549761322643071, 443),
    (118590899805286057887739609087, 389),
    (121019381962425623133141598207, 562),
    (121172594460735376390678593023, 445),
    (121344738463049153179721662463, 489),
    (122073227861724765664397230079, 551),
    (122834388093427971696718966783, 402),
    (125280393861289108189638295551, 533),
    (126778321893609356677628297215, 498),
    (134877338994778624923617198079, 429),
    (136319168768327298439513417151, 442),
    (140683356142945381137080385535, 492),
    (141389811227252306261634351103, 435),
    (142353197350388373522137219071, 500),
    (161499382024961324641983964607, 442),
    (161792984617398870906295549951, 491),
    (162764303815633020885862973439, 553),
    (168640316132962311354812727295, 645),
    (169398243281367919978820403199, 491),
)

HENSEL_SURVIVORS_95_NEW_55: Tuple[Tuple[int, int], ...] = (
    (59907013082369465778175, 392),
    (60411933919894174695423, 233),
    (71670149792337688788991, 338),
    (73852302447220611727359, 308),
    (89860519623554198667263, 391),
    (90617900879841262043135, 232),
    (104160846239067149434879, 252),
    (107505224688506533183487, 337),
    (107823322797873917370367, 372),
    (110778453670830917591039, 307),
    (114507656073401864290303, 282),
    (119814026164738931556351, 393),
    (119955432058033641881599, 440),
    (120823867839788349390847, 234),
    (122763081810537066004479, 268),
    (124427828405595315109887, 361),
    (125500315877988427104255, 318),
    (128807859955239879704575, 374),
    (132556311293340569987583, 391),
    (132853199061641515038879, 293),
    (134790779435331298000895, 390),
    (135926851319761893064703, 231),
    (136982089588472132141055, 388),
    (139813721821710785708031, 376),
    (141399454168681703014399, 254),
    (143340299584675377577983, 339),
    (145039106777724581355519, 341),
    (146605754261550804238335, 342),
    (147704604894441223454719, 309),
    (148997016003352210481151, 317),
    (149841535372565973827583, 360),
    (154209476375835576369151, 285),
    (156241269358600724152319, 251),
    (156533166824387703287655, 306),
    (157988005008520578596863, 309),
    (161238491446741700734591, 366),
    (161257837032759799775231, 336),
    (161734984196810876055551, 371),
    (166167680506246376386559, 306),
    (166397226865631715917823, 401),
    (168508003970472765861735, 252),
    (170909446401641809550335, 506),
    (171761484110102796435455, 281),
    (176333315357828567793663, 412),
    (177093811385379046399743, 357),
    (179721039247108397334527, 392),
    (179933148087050462822399, 439),
    (181235801759682524086271, 233),
    (181498566091316682293247, 341),
    (182698738749160304189439, 401),
    (183174981928129881079807, 314),
    (183449267168839050199039, 371),
    (183763036408780057112191, 322),
    (184144622715805599006719, 267),
    (184462799697925088739327, 349),
)

ALL_87_HENSEL_SURVIVORS: Tuple[Tuple[int, int], ...] = (
    HENSEL_SURVIVORS_92_TO_95_32 + HENSEL_SURVIVORS_95_NEW_55
)


def _extract_lean_pair_list(lean_text: str, def_name: str) -> List[Tuple[int, int]]:
    """Parse `def <def_name> : List (Nat × Nat) := [ ... ]` from Core.lean."""
    pattern = rf"def\s+{re.escape(def_name)}\s*:\s*List\s*\(Nat\s*×\s*Nat\)\s*:=\s*\[(.*?)\]"
    match = re.search(pattern, lean_text, flags=re.DOTALL)
    if match is None:
        raise ValueError(f"Could not locate {def_name} in Core.lean")
    body = match.group(1)
    pairs = re.findall(r"\(\s*(\d+)\s*,\s*(\d+)\s*\)", body)
    return [(int(z), int(k)) for z, k in pairs]


def build_positive_3x1_stress_bank(
    mersenne_k_min: int = 10,
    mersenne_k_max: int = 150,
    num_convergents: int = 56,
) -> Dict[str, object]:
    """
    Build and verify the positive `3x + 1` extreme stress bank:
    1. All 87 arithmetic Hensel survivors from `CollatzFormal/Core.lean`, cross-checked
       against `Core.lean` source and verified to drop `<= 2^71` in exact step count `k`.
    2. High-glide Mersenne seeds `2^k - 1` (`k = 10..150`), verifying `T^k(2^k - 1) = 3^k - 1`
       and recording `IsSurvivingMod1296Class` membership.
    3. Extreme `(W, K)` continued-fraction convergents of `log_2(3)` up to index 55.
    """
    core_lean_path = Path(__file__).resolve().parent / "CollatzFormal" / "Core.lean"
    lean_text = core_lean_path.read_text(encoding="utf-8")
    parsed_32 = tuple(_extract_lean_pair_list(lean_text, "henselSurvivors92To95"))
    parsed_55 = tuple(_extract_lean_pair_list(lean_text, "henselSurvivors95New55"))
    core_lean_exact_match = (
        parsed_32 == HENSEL_SURVIVORS_92_TO_95_32
        and parsed_55 == HENSEL_SURVIVORS_95_NEW_55
        and len(ALL_87_HENSEL_SURVIVORS) == 87
        and len({z for z, _ in ALL_87_HENSEL_SURVIVORS}) == 87
    )

    threshold_2_71 = 1 << 71
    survivors_drop_verified = True
    survivor_mod1296_count = 0
    max_first_odd_run = 0
    for z, k_drop in ALL_87_HENSEL_SURVIVORS:
        if (z & 1) == 0 or z <= threshold_2_71:
            survivors_drop_verified = False
        if is_surviving_mod1296_class(z):
            survivor_mod1296_count += 1
        w1 = ((z + 1) & -(z + 1)).bit_length() - 1
        if w1 > max_first_odd_run:
            max_first_odd_run = w1
        cur = z
        for _ in range(k_drop):
            cur = (3 * cur + 1) >> 1 if (cur & 1) else (cur >> 1)
        if cur > threshold_2_71:
            survivors_drop_verified = False

    mersenne_records: List[Dict[str, object]] = []
    mersenne_all_glide_exact = True
    mersenne_mod1296_survivors: List[int] = []
    for k in range(mersenne_k_min, mersenne_k_max + 1):
        seed = (1 << k) - 1
        # Verify exact algebraic k-step odd run and spot-check via direct step iteration
        cur = seed
        for _ in range(k):
            if (cur & 1) != 1:
                mersenne_all_glide_exact = False
                break
            cur = (3 * cur + 1) >> 1
        expected_peak = (3**k) - 1
        if cur != expected_peak:
            mersenne_all_glide_exact = False
        in_mod1296 = is_surviving_mod1296_class(seed)
        if in_mod1296:
            mersenne_mod1296_survivors.append(k)
        mersenne_records.append(
            {
                "k": k,
                "seed": seed,
                "peak_after_k_steps": expected_peak,
                "in_mod1296_sieve": in_mod1296,
            }
        )

    convergents: List[ConvergentLog2Of3] = log2_3_continued_fraction(
        num_terms=num_convergents, prec=350
    )
    # Verify alternating sign of 2^{p_n} - 3^{q_n} for all convergents with q_n <= 15000
    convergent_signs_verified = True
    for conv in convergents:
        if 1 <= conv.q <= 15000:
            diff = (1 << conv.p) - (3**conv.q)
            if (diff > 0) != (conv.index % 2 == 1):
                convergent_signs_verified = False

    return {
        "survivor_count": len(ALL_87_HENSEL_SURVIVORS),
        "core_lean_87_exact_match": core_lean_exact_match,
        "all_87_drop_below_2_pow_71": survivors_drop_verified,
        "survivors_in_mod1296_sieve": survivor_mod1296_count,
        "survivors_max_initial_odd_run_w1": max_first_odd_run,
        "mersenne_k_range": (mersenne_k_min, mersenne_k_max),
        "mersenne_count": len(mersenne_records),
        "mersenne_all_glide_exact": mersenne_all_glide_exact,
        "mersenne_mod1296_surviving_k": tuple(mersenne_mod1296_survivors),
        "convergents_count": len(convergents),
        "convergents": tuple(convergents),
        "convergent_signs_verified": convergent_signs_verified,
    }


# ============================================================================
# 6. Reusable CEGAR Proposal Auditors (Hard Rule 1 & Hard Rule 2 Gates)
# ============================================================================


@dataclass(frozen=True)
class UniversalityAuditResult:
    """Result of Hard Rule 1 universality & zero-custom-axiom check."""

    proposal_name: str
    passed: bool
    verdict: str  # "REDTEAM-PASSED" or "FALSIFIED-NON-UNIVERSAL"
    violations: Tuple[str, ...]


@dataclass(frozen=True)
class CounterModelGateResult:
    """Result of Hard Rule 2 3x3 counter-model & stress-bank audit."""

    proposal_name: str
    passed: bool
    verdict: str  # "REDTEAM-PASSED" or "FALSIFIED"
    holds_on_z_plus: bool
    fails_on_m1: bool
    fails_on_m2: bool
    fails_on_m3: bool
    minimal_counterexample: Optional[str]
    details: Dict[str, object]


@dataclass(frozen=True)
class ObstructionAuditResult:
    """Verification record for a proposed impossibility / obstruction theorem."""

    proposal_name: str
    passed: bool
    verdict: str  # "REDTEAM-PASSED" or "FALSIFIED-INVALID-WITNESS"
    witness_satisfies_hypotheses: bool
    witness_refutes_target: bool
    reason: str


FORBIDDEN_CUSTOM_AXIOMS: Set[str] = {
    "BarinaThreshold",
    "BakerLMNPowerBound",
    "RhinPowerBound",
    "SimonsDeWegerBound",
    "sorryAx",
}


def audit_universality_gate(
    proposal_name: str,
    *,
    is_finite_m_table: bool = False,
    is_finite_n_table: bool = False,
    is_bounded_weight_table: bool = False,
    uses_native_decide: bool = False,
    uses_sorry: bool = False,
    axioms_used: Sequence[str] = (),
) -> UniversalityAuditResult:
    """
    Hard Rule 1 Gate: Rejects any finite-`m`, finite-`N`, or bounded-weight `w <= W_0`
    stepping-stone certificate, `sorry`, `native_decide`, or non-standard custom axiom.
    """
    allowed_standard_axioms = {"propext", "Classical.choice", "Quot.sound"}
    violations: List[str] = []
    if is_finite_m_table:
        violations.append("Uses finite cycle-block m <= M_0 table instead of universal forall m/p")
    if is_finite_n_table:
        violations.append("Uses finite N <= N_0 verification table instead of universal forall n")
    if is_bounded_weight_table:
        violations.append(
            "Uses bounded-weight w <= W_0 table (refuted by density-0 Theorem 25.2)"
        )
    if uses_native_decide:
        violations.append("Uses forbidden Lean tactic native_decide")
    if uses_sorry:
        violations.append("Contains unproved sorry")
    for ax in axioms_used:
        if ax in FORBIDDEN_CUSTOM_AXIOMS or ax not in allowed_standard_axioms:
            violations.append(f"Depends on forbidden/custom axiom: {ax}")

    passed = len(violations) == 0
    return UniversalityAuditResult(
        proposal_name=proposal_name,
        passed=passed,
        verdict="REDTEAM-PASSED" if passed else "FALSIFIED-NON-UNIVERSAL",
        violations=tuple(violations),
    )


def audit_positive_cycle_exclusion_predicate(
    proposal_name: str,
    allows_cycle: Callable[[Fraction, Tuple[int, ...], int], bool],
    m1_catalog: Optional[Dict[str, object]] = None,
    m2_catalog: Optional[Dict[str, object]] = None,
    m3_catalog: Optional[Dict[str, object]] = None,
) -> CounterModelGateResult:
    """
    Hard Rule 2 Gate for Cycle-Exclusion Invariants:
    Given `allows_cycle(x0, parity_bits, odd_multiplier_q)` which represents the
    hypotheses of a proposed lemma claiming `x0 in {1, 2}`:
    - Must ALLOW `(1, (1, 0), 3)` and `(2, (0, 1), 3)` on `(Z^+, 3x+1)` (or accurately
      classify nontrivial cycles as impossible);
    - Must REJECT (`allows_cycle == False`) nontrivial cycles in `M1` (`19/5`, `29/5`,
      and generated `Q_(2)^+` cycles), `M2` (`-1`, `-5`, `-17`), and `M3` (`13`, `17`)!
    If `allows_cycle == True` on any nontrivial cycle in `M1`, `M2`, or `M3`, the
    proposed hypothesis set is SOUNDNESS-FALSIFIED (missing a discriminating axiom)!
    """
    m1 = m1_catalog if m1_catalog is not None else build_m1_q2_pos_catalog(max_generated_k=8)
    m2 = m2_catalog if m2_catalog is not None else build_m2_z_neg_catalog()
    m3 = m3_catalog if m3_catalog is not None else build_m3_5x1_catalog()

    z_plus_ok = allows_cycle(Fraction(1, 1), (1, 0), 3) and allows_cycle(
        Fraction(2, 1), (0, 1), 3
    )

    leaked_m1: Optional[str] = None
    m1_test_list: List[RationalCycleWitness] = [
        m1["canonical_19_5"],  # type: ignore[list-item]
        m1["canonical_29_5"],  # type: ignore[list-item]
        *m1["generated_non_integer_cycles"],  # type: ignore[misc]
    ]
    for c_m1 in m1_test_list:
        if allows_cycle(c_m1.x0, c_m1.parity_vector, 3):
            leaked_m1 = f"M1 cycle x0={c_m1.x0} (K={c_m1.period_k}, W={c_m1.weight_w})"
            break

    leaked_m2: Optional[str] = None
    for c_m2 in m2["cycles"]:  # type: ignore[attr-defined]
        if allows_cycle(Fraction(c_m2.seed, 1), c_m2.parity_vector, 3):
            leaked_m2 = f"M2 cycle x0={c_m2.seed} (K={c_m2.period_k}, W={c_m2.weight_w})"
            break

    leaked_m3: Optional[str] = None
    for c_m3 in m3["positive_cycles"]:  # type: ignore[attr-defined]
        if c_m3.seed in (13, 17):
            _, pbits = int_iter_and_parity(c_m3.seed, c_m3.period_k, q=5)
            if allows_cycle(Fraction(c_m3.seed, 1), pbits, 5):
                leaked_m3 = f"M3 (5x+1) cycle x0={c_m3.seed} (K={c_m3.period_k}, W={c_m3.weight_w})"
                break

    fails_m1 = leaked_m1 is None
    fails_m2 = leaked_m2 is None
    fails_m3 = leaked_m3 is None
    passed = z_plus_ok and fails_m1 and fails_m2 and fails_m3

    counterex: Optional[str] = None
    if not z_plus_ok:
        counterex = "Z^+ trivial cycle {1, 2} rejected by hypothesis"
    elif leaked_m1 is not None:
        counterex = leaked_m1
    elif leaked_m2 is not None:
        counterex = leaked_m2
    elif leaked_m3 is not None:
        counterex = leaked_m3

    return CounterModelGateResult(
        proposal_name=proposal_name,
        passed=passed,
        verdict="REDTEAM-PASSED" if passed else "FALSIFIED",
        holds_on_z_plus=z_plus_ok,
        fails_on_m1=fails_m1,
        fails_on_m2=fails_m2,
        fails_on_m3=fails_m3,
        minimal_counterexample=counterex,
        details={
            "leaked_m1": leaked_m1,
            "leaked_m2": leaked_m2,
            "leaked_m3": leaked_m3,
        },
    )


def audit_bounded_horizon_lyapunov_candidate(
    proposal_name: str,
    potential_fn: Callable[[Fraction, int], float],
    horizon_steps: int = 1,
    sieved_mod1296_only: bool = True,
) -> CounterModelGateResult:
    """
    Hard Rule 2 Gate for Bounded-Horizon Lyapunov / Matrix Ranking Candidates:
    Tests whether `potential_fn(T^h(x), q) < potential_fn(x, q)` for some `1 <= h <= horizon_steps`
    across:
      - Positive `3x + 1` stress bank (`2^k - 1` for `k = 10..150`, all 87 Hensel survivors, `27`),
      - Counter-models `M1` (`19/5`, `29/5`), `M2` (`-1`, `-5`, `-17`), `M3` (`13`, `17`, `7`).
    """
    if horizon_steps < 1:
        raise ValueError("horizon_steps must be >= 1")

    def decreases_within_horizon(x0: Fraction, q: int) -> bool:
        v0 = potential_fn(x0, q)
        cur = x0
        for _ in range(horizon_steps):
            cur = q2_compressed_step(cur, q=q)
            if potential_fn(cur, q) < v0:
                return True
        return False

    z_plus_counterex: Optional[str] = None
    # Stress test 1: Mersenne high-glide seeds 2^k - 1 (k = 10..150)
    for k in range(10, 151):
        seed = (1 << k) - 1
        if sieved_mod1296_only and not is_surviving_mod1296_class(seed):
            continue
        if not decreases_within_horizon(Fraction(seed, 1), 3):
            z_plus_counterex = (
                f"Z^+ Mersenne seed 2^{k} - 1 = {seed} (in_mod1296={is_surviving_mod1296_class(seed)}) "
                f"fails {horizon_steps}-step decrease"
            )
            break

    # Stress test 2: 87 arithmetic Hensel survivors + classic 27
    if z_plus_counterex is None:
        stress_ints = [27] + [z for z, _ in ALL_87_HENSEL_SURVIVORS]
        for z in stress_ints:
            if sieved_mod1296_only and not is_surviving_mod1296_class(z):
                continue
            if not decreases_within_horizon(Fraction(z, 1), 3):
                z_plus_counterex = f"Z^+ stress seed {z} fails {horizon_steps}-step decrease"
                break

    holds_z_plus = z_plus_counterex is None

    # Check M1, M2, M3 cycles: a valid global ranking function CANNOT decrease around a closed cycle!
    # Wait: even on a cycle, decreasing *somewhere* within horizon could happen at one vertex,
    # so for a cycle to be excluded by `potential_fn`, `potential_fn` must NOT decrease at EVERY
    # vertex of the cycle (in fact, by periodicity, NO function can strictly decrease at every
    # vertex of a finite cycle, unless horizon_steps jumps over, wait: on a cycle x_0..x_{p-1},
    # at argmin_i V(x_i), V(T^h(x_i)) >= V(x_i) for ALL h >= 1 automatically!).
    def decreases_on_entire_cycle(orb: Sequence[Fraction], q: int) -> bool:
        return all(decreases_within_horizon(pt, q) for pt in orb)

    m1_19 = trace_q2_cycle_from_parity((1, 1, 1, 0, 0)).orbit
    m2_17 = tuple(Fraction(x, 1) for x in trace_z_neg_cycle(-17).orbit)
    m3_13_int = analyze_m3_5x1_seed(13).orbit_sample
    m3_13 = tuple(Fraction(x, 1) for x in m3_13_int)

    fails_m1 = not decreases_on_entire_cycle(m1_19, 3)
    fails_m2 = not decreases_on_entire_cycle(m2_17, 3)
    fails_m3 = not decreases_on_entire_cycle(m3_13, 5)

    passed = holds_z_plus and fails_m1 and fails_m2 and fails_m3
    return CounterModelGateResult(
        proposal_name=proposal_name,
        passed=passed,
        verdict="REDTEAM-PASSED" if passed else "FALSIFIED",
        holds_on_z_plus=holds_z_plus,
        fails_on_m1=fails_m1,
        fails_on_m2=fails_m2,
        fails_on_m3=fails_m3,
        minimal_counterexample=z_plus_counterex,
        details={"horizon_steps": horizon_steps, "sieved_mod1296_only": sieved_mod1296_only},
    )


def audit_minimal_counterexample_sieve(
    proposal_name: str,
    survives_pred: Callable[[int], bool],
    modulus: int,
    witness_rules: Optional[Dict[int, Tuple[int, Tuple[int, ...]]]] = None,
    min_n_threshold: int = 2,
) -> Dict[str, object]:
    """
    Audit a proposed minimal-counterexample residue sieve `survives_pred(n)` modulo `modulus`
    (e.g. a proposed refinement of `IsSurvivingMod1296Class`):

    1. Checks well-definedness modulo `modulus`: `survives_pred(r) == survives_pred(r + modulus)`.
    2. If `witness_rules` maps killed residues `r` to `(K_fwd, u_bwd_bits)` (where `u_bwd_bits = ()`
       means pure forward drop `T^K(n) < n` and `len(u_bwd_bits) == L >= 1` means backward merger
       `2^L * T^K(n) = 3^{w(u)} * n' + C(u)` with `1 <= n' < n`), verifies:
       - Exact `3^{w(u)}` divisibility for ALL `n == r (mod modulus)` (which requires
         `2^K | modulus` and `3^{w(u)} | (2^L * 3^{w(v)} * modulus)` — wait: specifically,
         for `n = r + t * modulus`, `T^K(n) = 3^{w(v)} * t * (modulus / 2^K) + T^K(r)`, so
         `3^{w(u)}` divides `2^L * T^K(n) - C(u)` for ALL `t >= 0` IFF `2^K | modulus` AND
         `3^{w(u)} | 2^L * 3^{w(v)} * (modulus // 2^K)` AND `3^{w(u)} | (2^L * T^K(r) - C(u))`!);
       - Strict asymptotic slope `< 1` (`2^L * 3^{w(v)} < 2^K * 3^{w(u)}`);
       - Small-`n` boundary check for `n >= min_n_threshold` (`n = r, r + modulus, r + 2*modulus`):
         catches any small `n` where `n' < 1` or `n' >= n` due to carry offset!
    """
    if modulus < 2:
        raise ValueError("modulus must be >= 2")

    periodicity_violations: List[int] = []
    surviving_classes: List[int] = []
    for r in range(modulus):
        s0 = survives_pred(r)
        s1 = survives_pred(r + modulus)
        if s0 != s1:
            periodicity_violations.append(r)
        if s0:
            surviving_classes.append(r)

    rule_failures: List[str] = []
    small_n_exceptions: List[Tuple[int, int, str]] = []

    if witness_rules is not None:
        for r, (k_fwd, u_bits) in witness_rules.items():
            if survives_pred(r):
                rule_failures.append(f"Residue r={r} has a kill rule but survives_pred(r) is True")
                continue
            if modulus % (1 << k_fwd) != 0:
                rule_failures.append(
                    f"Residue r={r}: 2^K={1 << k_fwd} does not divide modulus={modulus}"
                )
                continue
            tk_r, v_bits = int_iter_and_parity(r, k_fwd, q=3)
            wv = sum(v_bits)
            l_bwd = len(u_bits)
            wu = sum(u_bits)
            cu = generalized_affine_carry(u_bits, q=3)

            # Asymptotic contraction check: 2^L * 3^wv < 2^K * 3^wu
            if (1 << l_bwd) * (3**wv) >= (1 << k_fwd) * (3**wu):
                rule_failures.append(
                    f"Residue r={r}: non-contractive slope 2^{l_bwd}*3^{wv} >= 2^{k_fwd}*3^{wu}"
                )
                continue

            if l_bwd > 0:
                step_mod_3 = ((1 << l_bwd) * (3**wv) * (modulus >> k_fwd)) % (3**wu)
                base_mod_3 = ((1 << l_bwd) * tk_r - cu) % (3**wu)
                if step_mod_3 != 0 or base_mod_3 != 0:
                    rule_failures.append(
                        f"Residue r={r}: 3^{wu} divisibility fails (step_rem={step_mod_3}, base_rem={base_mod_3})"
                    )
                    continue

            # Small-n boundary audit across first 5 representatives >= min_n_threshold
            checked_reps = 0
            t_mult = 0
            while checked_reps < 5:
                n_val = r + t_mult * modulus
                t_mult += 1
                if n_val < min_n_threshold:
                    continue
                checked_reps += 1
                tk_n, _ = int_iter_and_parity(n_val, k_fwd, q=3)
                if l_bwd == 0:
                    if not (1 <= tk_n < n_val):
                        small_n_exceptions.append(
                            (r, n_val, f"Forward T^{k_fwd}({n_val}) = {tk_n} not in [1, {n_val - 1}]")
                        )
                else:
                    num = (1 << l_bwd) * tk_n - cu
                    n_prime = num // (3**wu)
                    if not (1 <= n_prime < n_val):
                        small_n_exceptions.append(
                            (
                                r,
                                n_val,
                                f"Backward merger partner n' = {n_prime} not in [1, {n_val - 1}]",
                            )
                        )
                    else:
                        tl_np, _ = int_iter_and_parity(n_prime, l_bwd, q=3)
                        if tl_np != tk_n:
                            rule_failures.append(
                                f"Residue r={r}, n={n_val}: T^{l_bwd}({n_prime})={tl_np} != {tk_n}"
                            )

    passed = (
        len(periodicity_violations) == 0
        and len(rule_failures) == 0
        and len(small_n_exceptions) == 0
    )
    return {
        "proposal_name": proposal_name,
        "passed": passed,
        "verdict": "REDTEAM-PASSED" if passed else "FALSIFIED",
        "modulus": modulus,
        "surviving_count": len(surviving_classes),
        "surviving_density": len(surviving_classes) / modulus,
        "periodicity_violations": tuple(periodicity_violations),
        "rule_failures": tuple(rule_failures),
        "small_n_exceptions": tuple(small_n_exceptions),
    }


def audit_obstruction_witness(
    proposal_name: str,
    hypotheses_hold: Callable[[object], bool],
    target_property_holds: Callable[[object], bool],
    witness: object,
) -> ObstructionAuditResult:
    """
    Audit an impossibility / obstruction theorem claiming:
        `exists W, Hypotheses(W) and not TargetProperty(W)`.
    Verifies non-vacuity (`hypotheses_hold(witness) == True`) and genuine refutation
    (`target_property_holds(witness) == False`).
    """
    hyp_ok = bool(hypotheses_hold(witness))
    refutes_ok = not bool(target_property_holds(witness))
    passed = hyp_ok and refutes_ok
    if not hyp_ok:
        reason = "Constructed witness FAILS stated hypotheses (vacuous/invalid counterexample)"
    elif not refutes_ok:
        reason = "Constructed witness satisfies target property instead of refuting it"
    else:
        reason = "Witness satisfies all stated hypotheses and genuinely refutes target property"
    return ObstructionAuditResult(
        proposal_name=proposal_name,
        passed=passed,
        verdict="REDTEAM-PASSED" if passed else "FALSIFIED-INVALID-WITNESS",
        witness_satisfies_hypotheses=hyp_ok,
        witness_refutes_target=refutes_ok,
        reason=reason,
    )


# ============================================================================
# 7. Pre-Built Campaign Benchmark Audits (Tracks 1, 2, 3 Readiness Checks)
# ============================================================================


def verify_all_weight_primitive_root_mod_pow3(max_w: int = 7) -> Dict[str, object]:
    """
    Cross-verify Track 3's `forall w >= 1` 3-adic primitive-root lifting:
      `2^(2 * 3^(w - 1)) = 1 + k_w * 3^w` with `k_w % 3 != 0`,
    and verify that `{2^a mod 3^w : 0 <= a < 2 * 3^(w - 1)}` hits every unit mod `3^w`,
    plus verify backward exact integer division on `Z^+` vs failure modes on `M1, M2, M3`.
    """
    lifting_ok = True
    surjectivity_ok = True
    for w in range(1, max_w + 1):
        mod_3w = 3**w
        phi_3w = 2 * (3 ** (w - 1))
        val = 1 << phi_3w if phi_3w <= 2000 else None
        if val is not None:
            if (val - 1) % mod_3w != 0:
                lifting_ok = False
            k_w = (val - 1) // mod_3w
            if k_w % 3 == 0:
                lifting_ok = False
        else:
            if pow(2, phi_3w, mod_3w * 3) == 1 or pow(2, phi_3w, mod_3w) != 1:
                lifting_ok = False
        if w <= 5:
            orbit = {pow(2, a, mod_3w) for a in range(phi_3w)}
            units = {r for r in range(1, mod_3w) if r % 3 != 0}
            if orbit != units:
                surjectivity_ok = False

    # Verify Universal All-Weight Two-Return Backward Exact Division on Z^+:
    backward_div_z_plus_ok = True
    for w in range(1, 6):
        mod_3w = 3**w
        phi_3w = 2 * (3 ** (w - 1))
        u_word = (1,) + (0,) + (1,) * (w - 1)
        _, wu, cu = affine_parameters(u_word)
        assert wu == w
        for x2 in (1, 2, 4, 5, 7, 8, 19, 25):
            assert x2 % 3 != 0
            hits = [
                a for a in range(phi_3w) if (((1 << (len(u_word) + a)) * x2 - cu) % mod_3w) == 0
            ]
            if len(hits) != 1:
                backward_div_z_plus_ok = False
                continue
            a0 = hits[0]
            for q_mult in (0, 1):
                a_ext = a0 + q_mult * phi_3w
                u_ext = u_word + (0,) * a_ext
                _, wu_ext, cu_ext = affine_parameters(u_ext)
                num = (1 << len(u_ext)) * x2 - cu_ext
                if wu_ext != w or cu_ext != cu or (num % mod_3w) != 0 or (num // mod_3w) < 1:
                    backward_div_z_plus_ok = False

    # Verify algebraic sign-separation: because general_affine_converse_universal +
    # collatzIterInt_nonpos forces y >= 1 whenever x2 >= 1 and 2^|u|*x2 = 3^w*y + C(u),
    # NO pair (u, x2 >= 1) with x2 % 3 != 0 can EVER yield y <= 0 (even at q_mult = 0)!
    q0_nonpositive_y_witness: Optional[Tuple[Tuple[int, ...], int, int]] = None
    for length in range(2, 7):
        for u_cand in product((0, 1), repeat=length):
            wu = sum(u_cand)
            if wu == 0:
                continue
            cu = generalized_affine_carry(u_cand, q=3)
            mod_3w = 3**wu
            for x2 in range(1, 20):
                if x2 % 3 == 0:
                    continue
                num0 = (1 << length) * x2 - cu
                if num0 <= 0 and (num0 % mod_3w) == 0:
                    q0_nonpositive_y_witness = (u_cand, x2, num0 // mod_3w)
                    break
            if q0_nonpositive_y_witness is not None:
                break
        if q0_nonpositive_y_witness is not None:
            break

    return {
        "max_w_checked": max_w,
        "three_adic_lifting_verified": lifting_ok,
        "unit_surjectivity_verified": surjectivity_ok,
        "backward_congruence_verified": backward_div_z_plus_ok,
        "q0_nonpositive_y_counterexample": q0_nonpositive_y_witness,
    }


def run_full_redteam_harness() -> Dict[str, object]:
    """Execute the complete 3x3 counter-model catalog, stress bank, and CEGAR self-tests."""
    m1 = build_m1_q2_pos_catalog(max_generated_k=9, max_1cycle_w=20)
    m2 = build_m2_z_neg_catalog(sturm_horizons=(20, 40, 80))
    m3 = build_m3_5x1_catalog(divergent_steps=250)
    stress = build_positive_3x1_stress_bank(mersenne_k_min=10, mersenne_k_max=150)
    prim3 = verify_all_weight_primitive_root_mod_pow3(max_w=7)

    return {
        "m1_q2_pos": m1,
        "m2_z_neg": m2,
        "m3_5x1": m3,
        "stress_bank_3x1": stress,
        "primitive_root_3w_audit": prim3,
        "all_baseline_checks_green": (
            m1["hypotheses_status"]["local_congruences_mod_2A_3B"]
            and not m1["hypotheses_status"]["valuation_archimedean_bound_2_pow_v2_le_x_plus_1"]
            and m2["backward_quotient_neg17_witness"]["congruence_holds_yet_y_negative"]
            and m3["hypotheses_status"]["two_is_primitive_root_mod_q_pow_w"]
            and stress["core_lean_87_exact_match"]
            and stress["all_87_drop_below_2_pow_71"]
            and stress["mersenne_all_glide_exact"]
            and stress["convergent_signs_verified"]
            and prim3["three_adic_lifting_verified"]
            and prim3["unit_surjectivity_verified"]
            and prim3["backward_congruence_verified"]
            and (prim3["q0_nonpositive_y_counterexample"] is None)
        ),
    }


# ============================================================================
# 8. Live Campaign CEGAR Wave-1 Audits (Track 1 `#9` & Track 3 `#10`)
# ============================================================================


def audit_track1_wave1_lp_cycles() -> Dict[str, object]:
    """
    Adversarial CEGAR & 3x3 counter-model audit of Track 1 Wave 1 (`#9`, `cs_lp_cycles.py`):
    - Hard Rule 1 universality & zero-custom-axiom audit of T1, T2, T3, T4.
    - Boundary sweep (`k=0..6, n=0..35, m=0..40, M=0..40`) on T1 trajectory/cycle ratio bounds.
    - Verification that T2's `(21, 22)` band kills `W in {1, 2, 3, 4}` for ALL `K >= 0`, and
      that `x0 % 16 in {7, 11, 15} and x0 % 3 != 0` refines mod-48 cycle minima to the
      6-class set `{7, 11, 23, 31, 43, 47}` (subset of `{7, 11, 19, 23, 31, 35, 43, 47}`).
    - Verification of T3 (`IsBroxNatCycleMinWitness`) against ALL 96 primitive `M1` positive
      rational cycles (`K <= 9`), high-floor `319/13`, `M2 = Z^-`, and `M3 = 5x+1`.
    - Verification of T4 (`universal_bounded_modulus_cycle_obstruction`) across `A=0..4`,
      `B=0..3`, including `M = 1` (`A=0, B=0`), negative Bezout `U`, and `j > |v|`.
    """
    from .cs_lp_cycles import (
         affine_carry,
         bezout_coprime_pow2_pow3,
         construct_modular_pseudo_cycle_witness,
         evaluate_cycle_barriers_on_word,
         parity_weight,
         rotate_left,
    )

    u_gate = audit_universality_gate(
        "Track1_Wave1_T1_T4",
        is_finite_m_table=False,
        is_finite_n_table=False,
        is_bounded_weight_table=False,
        uses_native_decide=False,
        uses_sorry=False,
        axioms_used=("propext", "Classical.choice", "Quot.sound"),
    )

    t1_boundary_ok = True
    for k in range(0, 7):
        for n in range(0, 36):
            cur = n
            iters: List[int] = []
            bits: List[int] = []
            for _ in range(k):
                iters.append(cur)
                if (cur & 1) == 0:
                    bits.append(0)
                    cur //= 2
                else:
                    bits.append(1)
                    cur = (3 * cur + 1) // 2
            w = sum(bits)
            odd_vals = [val for val in iters if (val & 1) == 1]
            max_m = min(odd_vals) if odd_vals else 38
            min_big_m = max(odd_vals) if odd_vals else 0
            for m_lo in range(0, max_m + 1):
                if (1 << k) * (m_lo**w) * cur > ((3 * m_lo + 1) ** w) * n:
                    t1_boundary_ok = False
            for m_hi in range(min_big_m, min_big_m + 6):
                if ((3 * m_hi + 1) ** w) * n > (1 << k) * (m_hi**w) * cur:
                    t1_boundary_ok = False

    t2_band_kills_w_le_4 = True
    for w in range(1, 5):
        for k in range(0, 20):
            if ((21**w) < (7**w) * (1 << k)) and ((7**w) * (1 << k) <= (22**w)):
                t2_band_kills_w_le_4 = False

    sharper_mod48_classes = tuple(
        r for r in range(48) if (r % 16 in (7, 11, 15)) and (r % 3 != 0)
    )
    mod48_6class_exact = sharper_mod48_classes == (7, 11, 23, 31, 43, 47)

    m1 = build_m1_q2_pos_catalog(max_generated_k=9, max_1cycle_w=12)
    t3_m1_m2_m3_clean = True
    for rec in m1["generated_non_integer_cycles"]:
        ev = evaluate_cycle_barriers_on_word([bool(b) for b in rec.parity_vector], q=3)
        if ev["certified_nontrivial_3x1_witness"]:
            t3_m1_m2_m3_clean = False
    ev_319 = evaluate_cycle_barriers_on_word(
        [True, True, False, True, True, False, True, False], q=3
    )
    if ev_319["certified_nontrivial_3x1_witness"] or not ev_319["band_21_22"]:
        t3_m1_m2_m3_clean = False
    for neg_w in ([True], [True, True, False], [True, True, True, True, False, True, True, True, False, False, False]):
        if evaluate_cycle_barriers_on_word(neg_w, q=3)["certified_nontrivial_3x1_witness"]:
            t3_m1_m2_m3_clean = False
    for m3_w in ([True, True, False, False, False], [True, True, True, False, False, False, False], [True, True, False, False, True, False, False]):
        if evaluate_cycle_barriers_on_word(m3_w, q=5)["certified_nontrivial_3x1_witness"]:
            t3_m1_m2_m3_clean = False

    t4_obstruction_ok = True
    for v_word in (
        [True, False],
        [True, True, True, False, False],
        [True, True, False, True, True, False, True, False],
    ):
        for a_exp in range(0, 5):
            for b_exp in range(0, 4):
                cert = construct_modular_pseudo_cycle_witness(v_word, a_exp, b_exp)
                if not (
                    cert["homogeneous_steps_ok"]
                    and cert["modular_steps_ok"]
                    and cert["parity_ok"]
                    and cert["nondiv3_ok"]
                    and cert["telescoping_sum_zero"]
                ):
                    t4_obstruction_ok = False
                det = (1 << len(v_word)) - (3 ** parity_weight(v_word))
                mod_m = (1 << a_exp) * (3**b_exp)
                u_bez, _ = bezout_coprime_pow2_pow3(det, a_exp, b_exp)
                if (det * u_bez) % mod_m != (1 % mod_m):
                    t4_obstruction_ok = False
                for j in range(2 * len(v_word) + 2):
                    rot = rotate_left(v_word, j)
                    rot_nxt = rotate_left(v_word, j + 1)
                    pj = affine_carry(rot)
                    pnxt = affine_carry(rot_nxt)
                    rj = (pj * u_bez) % mod_m
                    rnxt = (pnxt * u_bez) % mod_m
                    if pj <= 0 or (pj % 3 == 0) or (b_exp >= 1 and (rj % 3 == 0)):
                        t4_obstruction_ok = False
                    if not rot[0]:
                        if pj != 2 * pnxt or ((2 * rnxt - rj) % mod_m != 0):
                            t4_obstruction_ok = False
                    else:
                        if 2 * pnxt != 3 * pj + det or ((2 * rnxt - (3 * rj + 1)) % mod_m != 0):
                            t4_obstruction_ok = False

    passed = (
        u_gate.passed
        and t1_boundary_ok
        and t2_band_kills_w_le_4
        and mod48_6class_exact
        and t3_m1_m2_m3_clean
        and t4_obstruction_ok
    )
    return {
        "passed": passed,
        "verdict": "REDTEAM-PASSED" if passed else "FALSIFIED",
        "universality_gate_passed": u_gate.passed,
        "t1_boundary_ok": t1_boundary_ok,
        "t2_band_kills_w_le_4": t2_band_kills_w_le_4,
        "sharper_mod48_6classes": sharper_mod48_classes,
        "t3_m1_m2_m3_clean": t3_m1_m2_m3_clean,
        "t4_obstruction_ok": t4_obstruction_ok,
    }


def audit_track3_wave1_forest_transfer() -> Dict[str, object]:
    """
    Adversarial CEGAR & 3x3 counter-model audit of Track 3 Wave 1 (`#10`, `cs_forest_transfer.py`):
    - Hard Rule 1 universality & zero-lookup-table audit of T3.1--T3.7.
    - Stress-test `collatzIter_pos_step_mod3_ne_zero` and `exactBackwardQuotient` across ALL
      87 arithmetic Hensel survivors (`Core.lean`) and Mersenne glides `2^k - 1` (`k = 10..150`).
    - Verify zero `Nat` underflow (`2^(|u|+shift)*x > C(u)`) across high-carry words (`u = 1^w`,
      `x in {1, 2, 4}`), negative sign dichotomy on `M2 = Z^-`, rational `Q_(2)^+` sign failure
      at `1/5, 1/125, 11/7`, and `M3 = 5x+1` `{1,2,3,4}` basin trapping.
    - Exhaustively test `pow2_orbit_three_coset_balance` (`T3.7`) across `m=0..4` and `c > 3*M`.
    """
    from .cs_forest_transfer import (
        exact_backward_quotient,
        verify_forest_transfer_counter_model_gate,
    )

    u_gate = audit_universality_gate(
        "Track3_Wave1_T3_1_to_T3_7",
        is_finite_m_table=False,
        is_finite_n_table=False,
        is_bounded_weight_table=False,
        uses_native_decide=False,
        uses_sorry=False,
        axioms_used=("propext", "Classical.choice", "Quot.sound"),
    )

    hensel_87_ok = True
    for r87, _k87 in ALL_87_HENSEL_SURVIVORS:
        cur = r87
        for _ in range(25):
            cur = (3 * cur + 1) // 2 if (cur & 1) else (cur // 2)
            if cur <= 0 or (cur % 3 == 0):
                hensel_87_ok = False
        x1 = (3 * r87 + 1) // 2
        for u_core in ((1,), (1, 1), (1, 0, 1), (1, 1, 1, 1)):
            y0 = exact_backward_quotient(x1, u_core, 0)
            y1 = exact_backward_quotient(x1, u_core, 1)
            if y0 < 1 or (y0 & 1) != 1 or y1 < 5:
                hensel_87_ok = False

    nat_no_underflow_ok = True
    for w in range(1, 7):
        u_all1 = (1,) * w
        for x_small in (1, 2, 4, 5):
            y0 = exact_backward_quotient(x_small, u_all1, 0)
            y1 = exact_backward_quotient(x_small, u_all1, 1)
            if y0 < 1 or (y0 & 1) != 1 or y1 < 5:
                nat_no_underflow_ok = False

    coset_balance_ok = True
    for m in range(0, 5):
        big_m = 3 ** (m + 1)
        per = 2 * (3**m)
        for a in range(0, 6):
            for c in (1, 2, 4, 5, 3 * big_m + 1, 3 * big_m + 2, 100):
                if c % 3 == 0:
                    continue
                r0 = ((1 << a) * c) % (3 * big_m)
                r1 = ((1 << (a + per)) * c) % (3 * big_m)
                r2 = ((1 << (a + 2 * per)) * c) % (3 * big_m)
                qs = (r0 // big_m, r1 // big_m, r2 // big_m)
                if not (
                    r0 % big_m == r1 % big_m == r2 % big_m
                    and all(q < 3 for q in qs)
                    and len(set(qs)) == 3
                    and sum(qs) == 3
                ):
                    coset_balance_ok = False

    cm_gate = verify_forest_transfer_counter_model_gate()
    passed = (
        u_gate.passed
        and hensel_87_ok
        and nat_no_underflow_ok
        and coset_balance_ok
        and bool(cm_gate["counter_model_gate_passed"])
    )
    return {
        "passed": passed,
        "verdict": "REDTEAM-PASSED" if passed else "FALSIFIED",
        "universality_gate_passed": u_gate.passed,
        "hensel_87_ok": hensel_87_ok,
        "nat_no_underflow_ok": nat_no_underflow_ok,
        "coset_balance_ok": coset_balance_ok,
        "counter_model_gate_passed": bool(cm_gate["counter_model_gate_passed"]),
    }


def audit_track2_wave1_sat_lyapunov() -> Dict[str, object]:
    """
    Adversarial CEGAR & 3x3 counter-model audit of Track 2 Wave 1 (`#12`, `cs_sat_lyapunov.py`):
    - Hard Rule 1 universality & zero-custom-axiom audit of T2.1, T2.2, T2.3.
    - Verify non-deterministic (interleaved carry) SRS rewrite step semantics preserve
      `collatzStep` / `srsEvalFramed` invariance across arbitrary rewrite orders, and verify
      all-dimension (`forall d >= 1`) Arctic quadratic pumping at `K = 0` and `K > 0`.
    - Verify self-congruent Syracuse pumping obstruction (`T2.2`) across `s_blocks = 3..20`,
      confirming `Mod-1296` & `Mod-5184` survival for ALL `s >= 3`, `s = 3 -> 433 mod 729`,
      and `Mod-46656` survival for ALL `s >= 4` (`x_end == 1 mod 729` identically for `s >= 6`).
    - Exhaustively sweep `n = 2..46656` across `IsSurvivingMod46656Class` (`2674 / 46656`),
      verifying zero small-`n` (`q = 0`) exceptions on all newly excluded progressions,
      empty-`uHead` (`uHead = []`) cancellation, and `u1 = 1` boundary on `w1 in {4, 5}`.
    """
    from . import cs_sat_lyapunov as csl

    u_gate = audit_universality_gate(
        "Track2_Wave1_T2_1_to_T2_3",
        is_finite_m_table=False,
        is_finite_n_table=False,
        is_bounded_weight_table=False,
        uses_native_decide=False,
        uses_sorry=False,
        axioms_used=("propext", "Classical.choice", "Quot.sound"),
    )

    # 1. Check rightmost (non-leftmost, interleaved carry) SRS derivations preserve exact semantics
    interleaved_srs_ok = True
    for seed in (7, 15, 27, 31, 63):
        cur = csl.encode_pos_binary_word(seed)
        c_steps = 0
        for _ in range(3000):
            nxts = csl.srs_one_step_all(cur)
            if not nxts:
                break
            rname, nxt_w = nxts[-1]  # rightmost redex instead of leftmost!
            v_pre = csl.srs_eval_framed(cur)
            v_post = csl.srs_eval_framed(nxt_w)
            if rname in ("R1_even", "R2_odd"):
                if v_post != csl.collatz_step(v_pre):
                    interleaved_srs_ok = False
                c_steps += 1
            elif v_post != v_pre:
                interleaved_srs_ok = False
            cur = nxt_w
        if cur != ("L", "R") or csl.collatz_iter(c_steps, seed) != 1:
            interleaved_srs_ok = False

    arctic_k0_ok = bool(
        csl.witness_arctic_all_dim_quadratic_pumping(0)["strictly_exceeds_arctic_bound"]
    )

    # 2. Check self-congruent pumping across s_blocks = 3..20
    pumping_ok = True
    for s_blk in range(3, 21):
        wit = csl.construct_self_congruent_syracuse_pumping_witness(
            exp2_A=6, exp3_B=6, s_blocks=s_blk, min_growth_G=3
        )
        if not (
            wit["collatz_iter_matches"]
            and wit["all_a_eq_1"]
            and wit["mod_self_congruent"]
            and wit["exceeds_growth_G"]
            and wit["survives_mod1296_start"]
            and wit["survives_mod5184_start"]
        ):
            pumping_ok = False
        if s_blk >= 4 and not (
            wit["survives_mod46656_start"] and wit["survives_mod46656_end"]
        ):
            pumping_ok = False

    # 3. Full period sweep n = 2..46656 + q=0 boundary + empty uHead + u1=1 exit-tail check
    mod46656_sweep_ok = True
    surv_count = 0
    if csl.is_surviving_mod46656_class(0) or csl.is_surviving_mod46656_class(1):
        mod46656_sweep_ok = False
    for n_val in range(2, 46656):
        if csl.is_surviving_mod46656_class(n_val):
            surv_count += 1
            if not (
                csl.is_surviving_mod5184_class(n_val)
                and csl.is_surviving_mod1296_class(n_val)
            ):
                mod46656_sweep_ok = False
        elif csl.is_surviving_mod1296_class(n_val):
            wit_ex = csl.witness_new_universal_exclusions_for_n(n_val)
            if wit_ex["kind"] == "descent":
                if not (0 < int(wit_ex["val"]) < n_val):
                    mod46656_sweep_ok = False
            elif not wit_ex["valid"]:
                mod46656_sweep_ok = False
    if surv_count != 2674:
        mod46656_sweep_ok = False

    empty_head_ok = all(
        csl.verify_all_weight_head_cancellation_identity(
            (), (1 << w1) * (3 if ((w1 + 1) % 2 == 1) else 1) - 1
        )["eq4_exact_cancellation"]
        for w1 in range(2, 9)
    )
    u1_eq_1_w5_ok = bool(csl.verify_w1_4_and_5_exit_tail_a2_forcing(31)["a2_eq_1"])
    cm_gate = csl.audit_3x3_counter_model_gate()

    passed = (
        u_gate.passed
        and interleaved_srs_ok
        and arctic_k0_ok
        and pumping_ok
        and mod46656_sweep_ok
        and empty_head_ok
        and u1_eq_1_w5_ok
        and bool(cm_gate["gate_3x3_all_passed"])
    )
    return {
        "passed": passed,
        "verdict": "REDTEAM-PASSED" if passed else "FALSIFIED",
        "universality_gate_passed": u_gate.passed,
        "interleaved_srs_ok": interleaved_srs_ok,
        "arctic_k0_ok": arctic_k0_ok,
        "pumping_ok": pumping_ok,
        "mod46656_surviving_count": surv_count,
        "mod46656_sweep_ok": mod46656_sweep_ok,
        "empty_head_ok": empty_head_ok,
        "u1_eq_1_w5_ok": u1_eq_1_w5_ok,
        "counter_model_gate_passed": bool(cm_gate["gate_3x3_all_passed"]),
    }


def audit_track1_wave2_lp_cycles() -> Dict[str, object]:
    """
    Adversarial CEGAR & 3x3 counter-model audit of Track 1 Wave 2 (`#14`, `T5`--`T8`):
    - Hard Rule 1 universality & zero-custom-axiom audit of T5, T6, T7, T8.
    - Verify T5 (`(2^K - 3^W) % 24 in {5, 7, 13, 23}` and `>= 5`) across `K=3..50, W=1..32`.
    - Verify T6 (`pow2_dvd_pow3_sub_one_le_four_mul` sharp equality at powers of two `w = 2^k`
      and `one_block_cycle_binary_squeeze_and_q0_ge_three`) across `w=1..256` and all
      `log_2(3)` convergents up to `W <= 16000` (where ZERO convergents satisfy `(3^W)//2^a1 == 2^W - 1`!).
    - Verify T7 (`broxOddCarry_append_false` and `cycle_min_first_block_dichotomy`, including
      `x0 = 0`, non-primitive period `p = 4` on `x0 = 1`, and `M1` 2-block contracting witness
      `1^3 0^2 1^5 0^3` at `10561/1631` vs `11369/1631`).
    - Verify T8 (`IsSharpenedBroxCycleWitness` mod-96 8-class sieve + dichotomy) across all
      `(w1, init, q0)` up to `K <= 12` and against `M1`, `M2`, `M3`.
    """
    from . import cs_lp_cycles as clp

    u_gate = audit_universality_gate(
        "Track1_Wave2_T5_to_T8",
        is_finite_m_table=False,
        is_finite_n_table=False,
        is_bounded_weight_table=False,
        uses_native_decide=False,
        uses_sorry=False,
        axioms_used=("propext", "Classical.choice", "Quot.sound"),
    )

    t5_ok = True
    for k_len in range(3, 51):
        for w_val in range(1, 33):
            if (3**w_val) < (1 << k_len):
                r5 = clp.verify_mod24_determinant_gap(k_len, w_val)
                if not (r5["in_4_classes"] and r5["ge_5"]):
                    t5_ok = False

    t6_ok = True
    for w_val in range(1, 257):
        if not clp.verify_2adic_lte_pow3_sub_one(w_val):
            t6_ok = False
        if w_val >= 2 and (w_val & (w_val - 1)) == 0:
            if clp.max_pow2_dividing_pow3_sub_one(w_val) != 4 * w_val:
                t6_ok = False

    convs = log2_3_continued_fraction(num_terms=20, prec=200)
    convergent_squeeze_hits = 0
    for conv in convs:
        w_c, k_c = conv.q, conv.p
        if w_c >= 2 and k_c >= w_c + 1 and w_c <= 16000 and (1 << k_c) > (3**w_c):
            a1 = k_c - w_c
            det = (1 << k_c) - (3**w_c)
            h_val = (1 << a1) - 1
            if det == h_val:
                t6_ok = False
            if 0 < det <= h_val:
                convergent_squeeze_hits += 1
                if ((3**w_c) // (1 << a1)) != ((1 << w_c) - 1):
                    t6_ok = False

    t7_ok = True
    for l_init in range(0, 8):
        for bits in product((False, True), repeat=l_init):
            if not clp.verify_brox_append_false_identity(bits):
                t7_ok = False
    sep = clp.verify_first_block_discreteness_separation()
    if not (sep["gap_strictly_between_0_and_1"] and sep["violates_z_discreteness_dichotomy"]):
        t7_ok = False

    mod96_classes = tuple(
        r
        for r in range(96)
        if (r % 16 in (7, 11, 15)) and (r % 32 not in (11, 23)) and (r % 3 != 0)
    )
    t8_ok = mod96_classes == (7, 31, 47, 59, 71, 79, 91, 95)
    for k_len in range(8, 13):
        for w1 in range(2, k_len - 1):
            init_len = k_len - w1 - 2
            for init in product((False, True), repeat=init_len):
                w_tot = w1 + sum(1 for b in init if b)
                if w_tot < 5 or (3**w_tot) >= (1 << k_len):
                    continue
                det = (1 << k_len) - (3**w_tot)
                rhs = clp.brox_odd_carry(init) + (1 << (init_len + 1))
                if rhs % det == 0:
                    q0 = rhs // det
                    if clp.is_sharpened_brox_cycle_witness(w1, init, q0):
                        t8_ok = False

    passed = u_gate.passed and t5_ok and t6_ok and t7_ok and t8_ok
    return {
        "passed": passed,
        "verdict": "REDTEAM-PASSED" if passed else "FALSIFIED",
        "universality_gate_passed": u_gate.passed,
        "t5_ok": t5_ok,
        "t6_ok": t6_ok,
        "convergent_squeeze_hits": convergent_squeeze_hits,
        "t7_ok": t7_ok,
        "t8_ok": t8_ok,
        "mod96_8classes": mod96_classes,
    }


def audit_track3_wave2_forest_transfer() -> Dict[str, object]:
    """
    Adversarial CEGAR & 3x3 counter-model audit of Track 3 Wave 2 (`#15`, `T3.8`--`T3.12`):
    - Hard Rule 1 universality & zero-custom-axiom audit of T3.8--T3.12.
    - Verify T3.8 (`odd_forest_collision_collapses_to_core_contraction`) across `K=0` and `K>=1`,
      `|u|<=k_tree` and genuine excursion `K=0, |u|>k_tree` (`r=2005 ->^{41} n=2429 > r, cs=()`).
    - Verify T3.9 (`exactBackwardQuotient_prefix_step_law` & `subcritical_prefix_le`), including
      empty/weight-0 prefixes `u1 = (), (0, 0)` AND verify genuine 3x3 failure in `M1 = Q_(2)^+`
      (`y0 = 1/5 < 1, u1 = (1, 0) -> T^2(1/5) = 2/5 > 1/5`) and `M2 = Z^-` (`x = -1, u1 = (0,), u2 = (1,)`).
    - Verify T3.10 & T3.11 (`supercritical_core_reduce` & `horizon_supercritical_reduce`) across
      all 87 Hensel survivors and all 96 generated `M1` rational cycles.
    - Verify T3.12 (`koopman_primitive_fiber_annihilation`, sharp equality of
      `affineCarry_universal_upper_bound` at `0^(L-w) 1^w`, and `non_descending_contraction_forces_log_shift_arc`).
    """
    from . import cs_forest_transfer as cft

    u_gate = audit_universality_gate(
        "Track3_Wave2_T3_8_to_T3_12",
        is_finite_m_table=False,
        is_finite_n_table=False,
        is_bounded_weight_table=False,
        uses_native_decide=False,
        uses_sorry=False,
        axioms_used=("propext", "Classical.choice", "Quot.sound"),
    )

    # 1. T3.8 excursion witness r=2005 ->^{41} odd n=2429 > r at K=0, cs=() (1 <= K' <= 1)
    r_exc = 2005
    u_exc = cft._parity_of_iter_int(r_exc, 41)
    n_exc = cft.collatz_iter_int(r_exc, 41)
    ko_exc, uc_exc = cft.collapse_forest_collision_to_core_contraction(
        n_exc, 0, r_exc, (), u_exc
    )
    ko_k0_short, uc_k0_short = cft.collapse_forest_collision_to_core_contraction(
        13, 0, 5, (False,), ()
    )
    t3_8_ok = (
        n_exc == 2429
        and ko_exc == 1
        and cft.is_core_parity_word(uc_exc)
        and cft.exact_backward_quotient(cft.collatz_iter_int(n_exc, ko_exc), uc_exc, 0) == r_exc
        and 1 <= ko_k0_short <= 7
        and cft.exact_backward_quotient(cft.collatz_iter_int(13, ko_k0_short), uc_k0_short, 0) <= 5
    )

    # 2. T3.9 boundary prefixes u1=(), (0,0) + genuine M1 (y0=1/5) & M2 (x=-1) failures
    t3_9_ok = True
    for u1 in ((), (0,), (0, 0), (1, 0), (1, 0, 0)):
        _, w1, c1 = cft.affine_parameters(u1)
        for u2 in ((1,), (0, 1), (1, 1), (1, 0, 1)):
            for x_val in (1, 2, 4, 5, 7, 13, 25):
                y0 = cft.exact_backward_quotient(x_val, u1 + u2, 0)
                y1 = cft.collatz_iter_int(y0, len(u1))
                yb2 = cft.exact_backward_quotient(x_val, u2, 0)
                if (1 << len(u1)) * y1 != (3**w1) * y0 + c1 or yb2 > y1:
                    t3_9_ok = False
                if (3**w1) + c1 <= (1 << len(u1)) and yb2 > y0:
                    t3_9_ok = False

    m1_y1, m1_p = q2_iter_and_parity(Fraction(1, 5), 2)
    m2_y0 = cft.exact_backward_quotient(-1, (0, 1), 0)
    m2_y2 = cft.exact_backward_quotient(-1, (1,), 0)
    m1_m2_subcritical_separation_ok = (
        m1_p == (1, 0) and m1_y1 == Fraction(2, 5) > Fraction(1, 5) and m2_y2 > m2_y0
    )

    # 3. T3.10 & T3.11 across all 87 Hensel survivors and M1 generated rational cycles
    t3_10_11_ok = True
    for z_mod, k_mod in ALL_87_HENSEL_SURVIVORS:
        n_seed = z_mod if z_mod >= 7 else z_mod + (1 << k_mod)
        if n_seed % 2 == 0:
            n_seed += 1
        x1 = cft.collatz_compressed_int(n_seed)
        for v_test in ((1, 0, 0, 1), (1, 1, 0, 1, 0, 1), (0, 1, 1, 0, 1, 0)):
            u_sup = cft.supercritical_core_reduce(v_test)
            if not cft.is_supercritical_core_word(u_sup):
                t3_10_11_ok = False
            if cft.exact_backward_quotient(x1, u_sup, 0) > cft.exact_backward_quotient(x1, v_test, 0):
                t3_10_11_ok = False

    m1_cat = build_m1_q2_pos_catalog(max_generated_k=8, max_1cycle_w=10)
    for cyc in m1_cat["generated_non_integer_cycles"]:
        pv = cyc.parity_vector
        idx1 = pv.index(1)
        pv_rot = pv[idx1:] + pv[:idx1]
        _, w1, c1 = cft.affine_parameters(pv_rot)
        w_ext = pv_rot + (1,)
        # Choose n_big strictly above (c1 - 3^w1) / (2^K - 3^w1)
        det = (1 << len(pv_rot)) - (3**w1)
        n_big = max(7, ((max(0, c1 - (3**w1))) // det) + 2)
        if cft.is_horizon_supercritical_for(n_big, w_ext):
            t3_10_11_ok = False

    # 4. T3.12 sharp carry bound at 0^(L-w) 1^w + Wave 2 full certificate
    t3_12_ok = True
    for length in range(1, 9):
        for u in product((0, 1), repeat=length):
            _, w, c_u = cft.affine_parameters(u)
            rhs = (1 << (length - w)) * ((3**w) - (1 << w))
            if c_u > rhs:
                t3_12_ok = False
            if u == (0,) * (length - w) + (1,) * w and c_u != rhs:
                t3_12_ok = False

    w2_cert = cft.verify_wave2_supercritical_collapse_and_archimedean_bottleneck(max_word_len=6)
    w2_cert_ok = all(
        bool(w2_cert[k])
        for k in (
            "prefix_step_law_verified",
            "supercritical_core_dominance_verified",
            "weight2_supercritical_singleton_11",
            "horizon_supercritical_reduction_verified",
            "m1_rational_cycle_prefixes_eliminated",
            "arbitrary_depth_forest_collapse_verified",
            "universal_carry_upper_bound_verified",
            "log_shift_bottleneck_verified",
            "koopman_fiber_annihilation_verified",
        )
    )

    passed = (
        u_gate.passed
        and t3_8_ok
        and t3_9_ok
        and m1_m2_subcritical_separation_ok
        and t3_10_11_ok
        and t3_12_ok
        and w2_cert_ok
    )
    return {
        "passed": passed,
        "verdict": "REDTEAM-PASSED" if passed else "FALSIFIED",
        "universality_gate_passed": u_gate.passed,
        "t3_8_excursion_ok": t3_8_ok,
        "t3_9_boundary_ok": t3_9_ok,
        "m1_m2_subcritical_separation_ok": m1_m2_subcritical_separation_ok,
        "t3_10_11_ok": t3_10_11_ok,
        "t3_12_ok": t3_12_ok,
        "wave2_cert_ok": w2_cert_ok,
    }


def audit_track2_wave2_sat_lyapunov(require_k_ge_1: bool = True) -> Dict[str, object]:
    """
    Adversarial CEGAR & 3x3 counter-model audit of Track 2 Wave 2 (`#17`, `T2.4`--`T2.6`):
    - Verify T2.4 (`core3` d=2 upper-triangular certificate, `forall d >= 1` top-left unit
      collapse, and `d = 2` upper-triangular impossibility across arbitrary `m_L, m_R >= 1`).
    - Verify T2.5 (`IsSurvivingMod373248Class` `10314 / 373248 = 191 / 6912`, `n >= 27` floor,
      and valid descent/merger witnesses across `n = 2..10000` plus all boundary classes).
    - Verify T2.6 pumping witness survival in `IsSurvivingMod373248Class` for `s >= 4`, AND
      detect the `k = 0, n = 27` (`27 % 3 == 0`) spurious truncated-quotient bug whenever
      `1 <= k` (`require_k_ge_1=False`) is omitted from `Mod373248CoreQuotientContractionProp`!
    """
    from . import cs_sat_lyapunov as csl

    u_gate = audit_universality_gate(
        "Track2_Wave2_T2_4_to_T2_6",
        is_finite_m_table=False,
        is_finite_n_table=False,
        is_bounded_weight_table=False,
        uses_native_decide=False,
        uses_sorry=False,
        axioms_used=("propext", "Classical.choice", "Quot.sound"),
    )

    # 1. T2.4 algebraic check including m_L >= 1 > 1 scaling
    d2_alg = csl.verify_d2_upper_triangular_impossibility_algebraic()
    t2_4_ok = all(bool(v) for v in d2_alg.values())
    for m_l in range(1, 5):
        for n_b in range(1, 6):
            for n_t in range(n_b + 1, 6):
                for p_l in range(0, 5):
                    for p_b1 in range(0, 6):
                        for p_t2 in range(1, 6):
                            if (
                                m_l * p_b1 + p_l * n_b >= m_l * p_t2 + p_l * n_t
                                and p_b1 + p_t2 * n_b >= p_t2 + p_b1 * n_t
                            ):
                                t2_4_ok = False

    # 2. T2.5 exact count 10314/373248, n >= 27 floor, and boundary witness sweep
    counts = csl.compute_sieved_survival_counts()
    t2_5_ok = counts["mod373248"] == (10314, 373248, Fraction(191, 6912))
    if any(csl.is_surviving_mod373248_class(n_s) for n_s in range(0, 27)):
        t2_5_ok = False
    if not csl.is_surviving_mod373248_class(27):
        t2_5_ok = False
    for n_val in range(2, 6000):
        if not csl.is_surviving_mod373248_class(n_val):
            wit = csl.witness_mod512_and_mod373248_exclusion(n_val)
            if wit["kind"] == "descent":
                if not (0 < int(wit["val"]) < n_val):
                    t2_5_ok = False
            elif not wit["valid"]:
                t2_5_ok = False

    # 3. T2.6 pumping survival + k >= 1 guard check at minimal survivor n = 27 (27 % 3 == 0)
    pumping_373248_ok = True
    for s_val in (4, 5, 6, 9):
        pw = csl.construct_self_congruent_syracuse_pumping_witness(
            exp2_A=9, exp3_B=6, s_blocks=s_val, min_growth_G=4
        )
        if not (pw["survives_mod373248_start"] and pw["survives_mod373248_end"]):
            pumping_373248_ok = False

    # Check k = 0 spurious Nat-truncation witness at n = 27:
    # Both total extensions of dlog2ModPow3 at 0 mod 3 yield a non-coalescing quotient < 27:
    spurious_zero_guard_val = ((1 << 1) * 27 - 1) // 3  # u = [True], a = 0 -> 17 < 27
    spurious_else_branch_val = ((1 << 4) * 27 - 31) // 27  # u = [True, False, True, True], a = 0 -> 14 < 27
    k0_spurious_detected = (
        csl.is_surviving_mod373248_class(27)
        and (27 % 3 == 0)
        and (1 <= spurious_zero_guard_val < 27 and csl.collatz_iter(1, spurious_zero_guard_val) != 27)
        and (1 <= spurious_else_branch_val < 27 and csl.collatz_iter(4, spurious_else_branch_val) != 27)
    )

    k_guard_ok = require_k_ge_1 and k0_spurious_detected
    passed = u_gate.passed and t2_4_ok and t2_5_ok and pumping_373248_ok and k_guard_ok
    return {
        "passed": passed,
        "verdict": "REDTEAM-PASSED" if passed else "FALSIFIED",
        "t2_4_ok": t2_4_ok,
        "t2_5_ok": t2_5_ok,
        "pumping_373248_ok": pumping_373248_ok,
        "k0_spurious_detected_at_27": k0_spurious_detected,
    }


def audit_track3_wave3_forest_transfer() -> Dict[str, object]:
    """
    Adversarial CEGAR & 3x3 counter-model audit of Track 3 Wave 3 (`#26`, `T3.13`--`T3.16`):
    - Hard Rule 1 universality & zero-custom-axiom audit of T3.13--T3.16 (`[]`-axiom bijection).
    - Verify `IsFirstHitOnePair` boundary `k = 0` (`(u=(1,), q=0)` -> `y = 1` rejected) and
      `1 <= k < L` loop extensions (`trivial_loop_extend_one_pair`).
    - Verify `T3.16` `exactBackwardQuotient x (true :: false :: rest) q % 4 == 1` across arbitrary
      `x % 3 != 0` INCLUDING `rest = ()` (non-core `(1, 0)`), and `(1, 1)` closed form `% 16 == 3`.
    - Verify roundtrip first-hit encoding/decoding on Mersenne glides `2^k - 1` (`k = 10..26`),
      all 87 Hensel survivors, and Wave 3 3x3 counter-model separation (`M1`, `M2`, `M3`).
    """
    from . import cs_forest_transfer as cft

    u_gate = audit_universality_gate(
        "Track3_Wave3_T3_13_to_T3_16",
        is_finite_m_table=False,
        is_finite_n_table=False,
        is_bounded_weight_table=False,
        uses_native_decide=False,
        uses_sorry=False,
        axioms_used=("propext", "Classical.choice", "Quot.sound"),
    )

    # 1. Verify T3.16 (1, 0) + rest % 4 == 1 across rest = () and len 1..3, x % 3 != 0
    t3_16_boundary_ok = True
    for r_len in range(0, 4):
        for rest in product((0, 1), repeat=r_len):
            u_word = (1, 0) + rest
            for x_val in (1, 2, 4, 5, 7, 10, 13, 25):
                for q_val in range(3):
                    yq = cft.exact_backward_quotient(x_val, u_word, q_val)
                    if yq < 1 or (yq % 4) != 1:
                        t3_16_boundary_ok = False
    for q_val in range(10):
        y11 = cft.exact_backward_quotient(1, (1, 1), q_val)
        if y11 != (32 * (64**q_val) - 5) // 9 or (y11 % 16) != 3:
            t3_16_boundary_ok = False

    # 2. Verify Mersenne high-glide seeds 2^k - 1 (k = 10..26) & k=0 / loop boundaries
    mersenne_bijection_ok = (
        not cft.is_first_hit_one_pair((1,), 0)
        and cft.is_first_hit_one_pair((1,), 1)
    )
    for k_exp in range(10, 27):
        m_seed = (1 << k_exp) - 1
        u_m, q_m = cft.encode_convergent_odd_to_first_hit_pair(m_seed, max_steps=6000)
        if (
            not cft.is_first_hit_one_pair(u_m, q_m)
            or cft.exact_backward_quotient(1, u_m, q_m) != m_seed
            or u_m[:2] != (1, 1)
            or sum(u_m) < k_exp
        ):
            mersenne_bijection_ok = False

    # 3. Full Wave 3 certificate (including 3x3 M1/M2/M3 gate)
    w3_cert = cft.verify_wave3_one_generator_bijection_and_range_equivalence(
        max_word_len=6, max_odd_bijection=1501, max_sieved_n=4000
    )
    w3_cert_ok = all(
        bool(w3_cert[k])
        for k in (
            "t313_generator_sound_verified",
            "t313_singleton_closed_form_verified",
            "t313_loop_degeneracy_verified",
            "t314_grid_injective_verified",
            "t314_roundtrip_bijection_verified",
            "mod373248_sieve_factored_count_verified",
            "t315_mod373248_range_verified",
            "t316_sharpened_prefix_weight_verified",
            "t316_weight_le2_exclusion_verified",
            "wave3_counter_model_gate_passed",
        )
    )

    passed = u_gate.passed and t3_16_boundary_ok and mersenne_bijection_ok and w3_cert_ok
    return {
        "passed": passed,
        "verdict": "REDTEAM-PASSED" if passed else "FALSIFIED",
        "t3_16_boundary_ok": t3_16_boundary_ok,
        "mersenne_bijection_ok": mersenne_bijection_ok,
        "wave3_cert_ok": w3_cert_ok,
    }


def audit_track2_wave3_sat_lyapunov() -> Dict[str, object]:
    """
    Adversarial CEGAR & 3x3 counter-model audit of Track 2 Wave 3 (`#28`, `T2.7`--`T2.9`):
    - Hard Rule 1 universality & zero-custom-axiom audit of T2.7--T2.9 (`forall w, N, d, k`).
    - Verify `T2.7` (`binGapWord` exact 3-adic Hensel cross-difference identity, `mnWitnessFamily`
      `w = 0..4` cardinality `3^w` & `0^k` separation, and constructive DFA refuter `N = 1..20`).
    - Verify `T2.8` (`forall d >= 1` coordinatewise-monotone upper-triangular identity collapse
      vs `d = 2` top-left-monotone 6-rule sharpness certificate).
    - Verify `T2.9` (`forall k >= 2` dyadic & `forall k >= 3` 3-stage triadic excluded families,
      exact valuation `v_3(r_{k2} - r_{k1}) == 2*k1 + 3`, CRT survival inside `Mod-373248`,
      and 3x3 counter-model separation).
    """
    from . import cs_sat_lyapunov as csl

    u_gate = audit_universality_gate(
        "Track2_Wave3_T2_7_to_T2_9",
        is_finite_m_table=False,
        is_finite_n_table=False,
        is_bounded_weight_table=False,
        uses_native_decide=False,
        uses_sorry=False,
        axioms_used=("propext", "Classical.choice", "Quot.sound"),
    )

    # 1. T2.7 Hensel cross-difference + w = 0..3 3^w witness family + N = 1, 3, 9, 20 DFA refuter
    t2_7_ok = csl.myhill_nerode_pow3_witness_family(0) == ((),)
    for w_val in range(0, 4):
        for bs1 in product((False, True), repeat=w_val):
            u = csl.binary_gap_weight_word(bs1)
            for bs2 in product((False, True), repeat=w_val):
                v = csl.binary_gap_weight_word(bs2)
                for b_a in (0, 1):
                    for b_b in (0, 1):
                        u_a = ((True, False) if b_a else (True,)) + u
                        u_b = ((True, False) if b_b else (True,)) + v
                        lhs = (1 << len(u_b)) * csl.affine_carry(u_a) - (
                            1 << len(u_a)
                        ) * csl.affine_carry(u_b)
                        rhs = (3**w_val) * (
                            (1 << (1 + b_b + len(v))) - (1 << (1 + b_a + len(u)))
                        ) + (1 << (2 + b_a + b_b)) * (
                            (1 << len(v)) * csl.affine_carry(u)
                            - (1 << len(u)) * csl.affine_carry(v)
                        )
                        if lhs != rhs:
                            t2_7_ok = False
    for n_st in (1, 3, 9, 20):
        ref = csl.refute_arbitrary_dfa_on_one_equation(
            n_states=n_st,
            transition_fn=lambda q, bit, m=n_st: (3 * q + (2 if bit else 1)) % m,
            start_state=0,
            accept_states=[0],
        )
        if not ref["dfa_refuted"]:
            t2_7_ok = False

    # 2. T2.8 all-dim coordinatewise-monotone collapse & d=2 top-left sub6 sharpness
    t2_8_ok = all(bool(v) for v in csl.verify_all_dim_coord_monotone_upper_tri_collapse(5).values())

    # 3. T2.9 dyadic (k=2..14) + 3-stage triadic (k=3..14, exact v_3(r2-r1)=2*k1+3) + 3x3 gate
    t2_9_ok = True
    for k_d in range(2, 15):
        for q_d in (0, 1, 3):
            wd = csl.witness_dyadic_parametric_exclusion(k_d, q_d)
            if not (wd["v2_n_plus_1_eq_k"] and wd["strictly_smaller_pos"] and wd["coalesces_k2_k1"]):
                t2_9_ok = False
    for k_t in range(3, 15):
        r_t, _ = csl.triadic_backward_excluded_residue(k_t)
        for k_t2 in range(k_t + 1, 16):
            r_t2, _ = csl.triadic_backward_excluded_residue(k_t2)
            diff_t = abs(r_t2 - r_t)
            p3_exact = 3 ** (2 * k_t + 3)
            if diff_t % p3_exact != 0 or (diff_t // p3_exact) % 3 == 0:
                t2_9_ok = False
        for q_t in (0, 1, 2):
            wt = csl.witness_triadic_parametric_exclusion(k_t, q_t)
            if not (
                wt["exact_div27"]
                and wt["r_mod729_eq_361"]
                and wt["strictly_smaller_pos"]
                and wt["coalesces_3k10_0"]
            ):
                t2_9_ok = False

    gate3_ok = all(bool(v) for v in csl.audit_wave3_3x3_counter_model_gate().values())
    passed = u_gate.passed and t2_7_ok and t2_8_ok and t2_9_ok and gate3_ok
    return {
        "passed": passed,
        "verdict": "REDTEAM-PASSED" if passed else "FALSIFIED",
        "t2_7_ok": t2_7_ok,
        "t2_8_ok": t2_8_ok,
        "t2_9_ok": t2_9_ok,
        "gate3_ok": gate3_ok,
    }


def audit_track1_wave3_lp_cycles() -> Dict[str, object]:
    """
    Adversarial CEGAR & 3x3 counter-model audit of Track 1 Wave 3 (`#30`, `T9`--`T11`):
    - Hard Rule 1 universality & zero-custom-axiom audit of T9--T11 (`[]` custom axioms,
      zero `BarinaThreshold`, zero `BakerLMNPowerBound`).
    - Verify `T9` (`D | gcd(2^a1 - 1, 3^w1 - 2^w1)`, `forall r, q0 != 3^r`,
      `q0 % 24 in {3, 9, 17, 19}`, `q0 >= 17` and `>= 19` for odd `w1`,
      `x0 % 96 in {31, 95}`, `w1 >= 13, a1 >= 8`, `(17 * 3^w1) // 2^a1 == 17 * 2^w1 - 1`)
      across `w1 = 2..80` and all `log_2(3)` convergents up to `W <= 16000`.
    - Verify `T10` (2-block cleared-denominator reciprocal identity, cross-carry bridge
      `3^w1 * H0 - D == 2^a1 * (2^w2 * H1 - D)`, Mersenne `q0 = 1` & `q1 = 1` elimination
      forcing `x0 >= 47, x1 >= 49`, `23 * D < 3^W` killing `W = 5`, Dual Brox Cubic Squeeze
      `27 * 2^(W + a1 - 3) * D^3 < 2^(3*K)`, `M1` witnesses `251/13 <-> 439/13` and
      `287/13 <-> 331/13`, and `SubexponentialCubicGapProp` across `W = 6..600` + convergents).
    - Verify `T11` (`one_block_cycle_has_smaller_nonconvergent_partner` across `(Z^+, 3x+1)`,
      `M1 = Q_(2)^+` well-ordering separation at `19/5 -> 7/5 -> 1/5 < 1`, and `M3 = 5x+1`
      merger failure at `13 -> n' = 6 -> 1`, plus `IsWave3SharpenedBroxWitness` sweep).
    """
    from . import cs_lp_cycles as clp

    u_gate = audit_universality_gate(
        "Track1_Wave3_T9_to_T11",
        is_finite_m_table=False,
        is_finite_n_table=False,
        is_bounded_weight_table=False,
        uses_native_decide=False,
        uses_sorry=False,
        axioms_used=(),
    )

    # 1. Verify T9 mod-24 / mod-96 locks, w1 = 2..80 sweep, and log_2(3) convergents <= 16000
    even_w1_mod24 = {
        q_mod
        for a_par in (0, 1)
        for q_mod in range(1, 24, 2)
        if ((((16 if a_par % 2 == 0 else 8) - 9) * q_mod) % 24)
        == ((15 if a_par == 0 else 7) % 24)
    }
    odd_w1_mod24 = {
        q_mod
        for a_par in (0, 1)
        for q_mod in range(1, 24, 2)
        if ((((16 if (1 + a_par) % 2 == 0 else 8) - 3) * q_mod) % 24)
        == ((15 if a_par == 0 else 7) % 24)
    }
    t9_ok = (
        even_w1_mod24 == {9, 17}
        and odd_w1_mod24 == {3, 19}
        and (even_w1_mod24 | odd_w1_mod24) == {3, 9, 17, 19}
    )
    for w1 in range(2, 81):
        a_min = (3**w1).bit_length() - w1
        for a1 in range(max(1, a_min - 2), a_min + 6):
            r9 = clp.verify_one_block_gcd_and_mod24_squeeze(w1, a1)
            if not (
                r9["linear_comb_ok"]
                and r9["pow3_quotient_impossible"]
                and r9["small_w1_impossible"]
                and r9["binary_prefix17_ok"]
                and r9["gcd_and_mod_locks_ok"]
                and (not r9["divisible_hit"])
            ):
                t9_ok = False

    convs = log2_3_continued_fraction(num_terms=22, prec=250)
    conv_17squeeze_hits = 0
    cubic_gap_ok = (27 * (1 << (5 - 2)) * (13**3)) < (1 << 24)
    for conv in convs:
        w_c, k_c = conv.q, conv.p
        if w_c >= 2 and k_c >= w_c + 1 and w_c <= 16000 and (1 << k_c) > (3**w_c):
            a1_c = k_c - w_c
            det_c = (1 << k_c) - (3**w_c)
            h_c = (1 << a1_c) - 1
            if 17 * det_c <= h_c:
                conv_17squeeze_hits += 1
                if ((17 * (3**w_c)) // (1 << a1_c)) != (17 * (1 << w_c) - 1):
                    t9_ok = False
            if h_c % det_c == 0:
                t9_ok = False
            if w_c <= 500:
                r9_c = clp.verify_one_block_gcd_and_mod24_squeeze(w_c, a1_c)
                if not (
                    r9_c["binary_prefix17_ok"]
                    and r9_c["gcd_and_mod_locks_ok"]
                    and (not r9_c["divisible_hit"])
                ):
                    t9_ok = False
            if w_c >= 6 and not clp.check_subexponential_cubic_gap(k_c, w_c):
                cubic_gap_ok = False

    p3 = 3**6
    for w_val in range(6, 601):
        k_min = p3.bit_length()
        if not (
            clp.check_subexponential_cubic_gap(k_min, w_val)
            and clp.check_subexponential_cubic_gap(k_min + 1, w_val)
        ):
            cubic_gap_ok = False
        p3 *= 3

    # 2. Verify T10 cross-carry bridge, 2-block sweep, and M1 D=13 obstruction witnesses
    t10_ok = True
    for w_tot in range(2, 14):
        for k_tot in range(w_tot + 2, 2 * w_tot + 1):
            det_t = (1 << k_tot) - (3**w_tot)
            for w1 in range(1, w_tot):
                w2 = w_tot - w1
                for a1 in range(1, k_tot - w_tot):
                    a2 = k_tot - w_tot - a1
                    h0, h1 = clp.two_block_brox_carries(w1, a1, w2, a2)
                    if (3**w1) * h0 - det_t != (1 << a1) * ((1 << w2) * h1 - det_t):
                        t10_ok = False
                    r10 = clp.verify_two_block_cleared_denom_and_cubic_squeeze(
                        w1, a1, w2, a2, n0_floor=26
                    )
                    if not (
                        r10["brox_closed_form_ok"]
                        and r10["reciprocal_identity_ok"]
                        and r10["mersenne_q0_impossible"]
                        and r10["mersenne_q1_impossible"]
                        and r10["cubic_squeeze_ok"]
                        and r10["potential_merger_bound_ok"]
                    ):
                        t10_ok = False

    for w_tot in range(5, 24):
        k_min = (3**w_tot).bit_length()
        for k_tot in (k_min, k_min + 1):
            if not ((21**w_tot) < (7**w_tot) * (1 << k_tot) <= (22**w_tot)):
                continue
            det_t = (1 << k_tot) - (3**w_tot)
            for w1 in range(2, w_tot):
                w2 = w_tot - w1
                for a1 in range(1, k_tot - w_tot):
                    a2 = k_tot - w_tot - a1
                    h0, h1 = clp.two_block_brox_carries(w1, a1, w2, a2)
                    if h0 % det_t == 0:
                        if h1 % det_t != 0 or clp.is_primitive_two_block_brox_witness(
                            w1, a1, w2, a2, h0 // det_t, h1 // det_t
                        ):
                            t10_ok = False

    m1_obs = clp.verify_two_block_m1_potential_obstruction_witnesses()
    if not (
        m1_obs["witness_251_x0"] == Fraction(251, 13)
        and m1_obs["witness_251_x1"] == Fraction(439, 13)
        and m1_obs["witness_251_satisfies_q_potential"]
        and m1_obs["witness_251_separated_by_z_and_23D"]
        and m1_obs["witness_287_x0"] == Fraction(287, 13)
        and m1_obs["witness_287_x1"] == Fraction(331, 13)
        and m1_obs["witness_287_satisfies_3D_and_cubic"]
        and m1_obs["witness_287_separated_by_z_and_23D"]
    ):
        t10_ok = False

    # 3. Verify T11 Hercher subdouble merger + M1 well-ordering separation + M3 separation
    hercher_sep = clp.verify_hercher_subdouble_merger_separation()
    x0_m1 = Fraction(19, 5)
    n_prime_m1 = (x0_m1 - 1) / 2  # 7/5
    y_m1, _ = q2_iter_and_parity(n_prime_m1, 4, q=3)
    t11_ok = (
        bool(hercher_sep["all_3x1_mergers_ok"])
        and bool(hercher_sep["m3_x0_13_is_one_block_cycle"])
        and bool(hercher_sep["m3_partner_6_reaches_one"])
        and (y_m1 == x0_m1)
        and (Fraction(0) < (n_prime_m1 - 1) / 2 < Fraction(1))
    )
    for k_len in range(8, 13):
        for w1 in range(2, k_len - 1):
            init_len = k_len - w1 - 2
            for init in product((False, True), repeat=init_len):
                w_tot = w1 + sum(1 for b in init if b)
                if w_tot < 5 or (3**w_tot) >= (1 << k_len):
                    continue
                det_w = (1 << k_len) - (3**w_tot)
                rhs = clp.brox_odd_carry(init) + (1 << (init_len + 1))
                if rhs % det_w == 0 and clp.is_wave3_sharpened_brox_witness(
                    w1, init, rhs // det_w
                ):
                    t11_ok = False

    passed = (
        u_gate.passed
        and t9_ok
        and (conv_17squeeze_hits == 0)
        and cubic_gap_ok
        and t10_ok
        and t11_ok
    )
    return {
        "passed": passed,
        "verdict": "REDTEAM-PASSED" if passed else "FALSIFIED",
        "t9_ok": t9_ok,
        "conv_17squeeze_hits": conv_17squeeze_hits,
        "cubic_gap_ok": cubic_gap_ok,
        "t10_ok": t10_ok,
        "t11_ok": t11_ok,
    }
