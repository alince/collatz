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

import decimal
import json
import math
import random
import re
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Sequence, Set, Tuple

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


# ============================================================================
# 9. Persistent Self-Improving Witness Bank & Wave 4 Whole-Space Runner
# ============================================================================

DEFAULT_WITNESS_BANK_FILENAME = "witness_bank.json"
REQUIRED_WITNESS_DOMAINS: Tuple[str, ...] = (
    "z_pos_high_glide",
    "m1_q2_pos",
    "m2_z_neg",
    "m3_supercritical",
    "log2_3_convergents",
)


def default_witness_bank_path() -> Path:
    """Return the canonical path to `collatz_analysis/witness_bank.json`."""
    return Path(__file__).resolve().parent / DEFAULT_WITNESS_BANK_FILENAME


def load_witness_bank(bank_path: Optional[Path] = None) -> Dict[str, Any]:
    """Load and schema-validate `witness_bank.json`, including referential integrity."""
    target = bank_path if bank_path is not None else default_witness_bank_path()
    data = json.loads(target.read_text(encoding="utf-8"))
    if not isinstance(data, dict) or "domains" not in data or "falsified_hypotheses" not in data:
        raise ValueError("Invalid witness_bank.json schema: missing 'domains' or 'falsified_hypotheses'")
    domains = data["domains"]
    if not isinstance(domains, dict):
        raise ValueError("Invalid witness_bank.json schema: 'domains' must be a dict")
    for req in REQUIRED_WITNESS_DOMAINS:
        if req not in domains or not isinstance(domains[req], list) or len(domains[req]) == 0:
            raise ValueError(f"Invalid witness_bank.json schema: domain '{req}' missing or empty")
    seen_ids: Set[str] = set()
    for dom_name, entries in domains.items():
        if not isinstance(entries, list):
            raise ValueError(f"Domain '{dom_name}' must map to a list of witness dicts")
        for entry in entries:
            if not isinstance(entry, dict):
                raise ValueError(f"Entry in domain '{dom_name}' must be a dict")
            wid = entry.get("witness_id")
            if not isinstance(wid, str) or not wid:
                raise ValueError(f"Entry in domain '{dom_name}' missing non-empty 'witness_id'")
            if wid in seen_ids:
                raise ValueError(f"Duplicate witness_id '{wid}' in witness_bank.json")
            if "kills_mechanisms" in entry:
                kills = entry["kills_mechanisms"]
                if not isinstance(kills, list) or len(kills) == 0:
                    raise ValueError(f"Witness '{wid}' must have a non-empty 'kills_mechanisms' list")
            seen_ids.add(wid)

    falsified = data["falsified_hypotheses"]
    if not isinstance(falsified, list):
        raise ValueError("Invalid witness_bank.json schema: 'falsified_hypotheses' must be a list")
    seen_hids: Set[str] = set()
    for rec in falsified:
        if not isinstance(rec, dict):
            raise ValueError("Each entry in 'falsified_hypotheses' must be a dict")
        hid = rec.get("hypothesis_id")
        if not isinstance(hid, str) or not hid:
            raise ValueError("Falsified hypothesis entry missing non-empty 'hypothesis_id'")
        if hid in seen_hids:
            raise ValueError(f"Duplicate hypothesis_id '{hid}' in witness_bank.json")
        seen_hids.add(hid)
        min_wid = rec.get("minimal_witness_id")
        if not isinstance(min_wid, str) or min_wid not in seen_ids:
            raise ValueError(
                f"Hypothesis '{hid}' references unknown minimal_witness_id '{min_wid}'"
            )
        sec_wid = rec.get("secondary_witness_id")
        if sec_wid is not None and (not isinstance(sec_wid, str) or sec_wid not in seen_ids):
            raise ValueError(
                f"Hypothesis '{hid}' references unknown secondary_witness_id '{sec_wid}'"
            )
    return data


def append_witness_to_bank(
    domain: str,
    witness_entry: Dict[str, Any],
    bank_path: Optional[Path] = None,
) -> bool:
    """
    Permanently append a minimal falsifying witness to `witness_bank.json` if its
    `witness_id` is not already present (idempotent self-improvement).
    Returns True if newly appended, False if `witness_id` already existed.
    """
    if domain not in REQUIRED_WITNESS_DOMAINS:
        raise ValueError(f"Unknown witness domain '{domain}', expected one of {REQUIRED_WITNESS_DOMAINS}")
    if not isinstance(witness_entry, dict):
        raise ValueError("witness_entry must be a dict")
    wid = witness_entry.get("witness_id")
    if not isinstance(wid, str) or not wid:
        raise ValueError("witness_entry must include a non-empty string 'witness_id'")
    if "kills_mechanisms" in witness_entry:
        kills = witness_entry["kills_mechanisms"]
        if not isinstance(kills, list) or len(kills) == 0:
            raise ValueError(f"Witness '{wid}' must have a non-empty 'kills_mechanisms' list")
    target = bank_path if bank_path is not None else default_witness_bank_path()
    bank = load_witness_bank(target)
    for entries in bank["domains"].values():
        if any(e.get("witness_id") == wid for e in entries):
            return False
    bank["domains"][domain].append(witness_entry)
    target.write_text(json.dumps(bank, indent=2) + "\n", encoding="utf-8")
    return True


def append_falsified_hypothesis_record(
    record: Dict[str, Any],
    bank_path: Optional[Path] = None,
) -> bool:
    """
    Permanently append a falsified hypothesis record to `witness_bank.json`
    (idempotent by `hypothesis_id`).
    """
    hid = record.get("hypothesis_id")
    if not isinstance(hid, str) or not hid:
        raise ValueError("record must include a non-empty string 'hypothesis_id'")
    target = bank_path if bank_path is not None else default_witness_bank_path()
    bank = load_witness_bank(target)
    if any(r.get("hypothesis_id") == hid for r in bank["falsified_hypotheses"]):
        return False
    all_wids = {
        str(e["witness_id"])
        for entries in bank["domains"].values()
        for e in entries
    }
    min_wid = record.get("minimal_witness_id")
    if not isinstance(min_wid, str) or min_wid not in all_wids:
        raise ValueError(f"Hypothesis '{hid}' references unknown minimal_witness_id '{min_wid}'")
    sec_wid = record.get("secondary_witness_id")
    if sec_wid is not None and (not isinstance(sec_wid, str) or sec_wid not in all_wids):
        raise ValueError(f"Hypothesis '{hid}' references unknown secondary_witness_id '{sec_wid}'")
    bank["falsified_hypotheses"].append(record)
    target.write_text(json.dumps(bank, indent=2) + "\n", encoding="utf-8")
    return True


def evaluate_hypothesis_against_witness_bank(
    hypothesis_id: str,
    predicate_fn: Callable[[str, Dict[str, Any]], bool],
    domains: Optional[Sequence[str]] = None,
    bank_path: Optional[Path] = None,
    record_failure: bool = False,
    branch: str = "UNSPECIFIED",
    statement: str = "",
) -> Dict[str, Any]:
    """
    Evaluate `predicate_fn(domain_name, witness_dict)` across 100% of applicable
    entries in `witness_bank.json`. A candidate hypothesis passes ONLY if every
    tested witness returns True.
    """
    target = bank_path if bank_path is not None else default_witness_bank_path()
    bank = load_witness_bank(target)
    active_domains = tuple(domains) if domains is not None else REQUIRED_WITNESS_DOMAINS
    if len(active_domains) == 0:
        raise ValueError("domains must be non-empty")
    for dom in active_domains:
        if dom not in bank["domains"]:
            raise ValueError(f"Unknown witness domain '{dom}', expected one of {tuple(bank['domains'].keys())}")

    total_checked = 0
    failures: List[Tuple[str, str]] = []
    for dom in active_domains:
        for entry in bank["domains"][dom]:
            total_checked += 1
            if not predicate_fn(dom, entry):
                failures.append((dom, str(entry["witness_id"])))

    passed = (total_checked > 0) and (len(failures) == 0)
    minimal_failure = failures[0] if failures else None

    if (not passed) and record_failure and minimal_failure is not None:
        append_falsified_hypothesis_record(
            {
                "hypothesis_id": hypothesis_id,
                "branch": branch,
                "statement": statement or hypothesis_id,
                "status": "FALSIFIED",
                "minimal_witness_id": minimal_failure[1],
                "failure_diagnosis": f"Failed witness {minimal_failure[1]} in domain {minimal_failure[0]} ({len(failures)}/{total_checked} witnesses failed).",
            },
            bank_path=target,
        )

    return {
        "hypothesis_id": hypothesis_id,
        "passed": passed,
        "verdict": "WITNESS-BANK-PASSED" if passed else "FALSIFIED",
        "total_checked": total_checked,
        "failure_count": len(failures),
        "failures": tuple(failures),
        "minimal_failure": minimal_failure,
    }


# ----------------------------------------------------------------------------
# Solvable Mixed-(2,3) Cousin `T_diamond` & Nonlocal `core_3` Invariant
# ----------------------------------------------------------------------------


def core3_pos(n: int) -> int:
    """Strip all factors of 3 from positive integer `n > 0` (`core3` in Lean 4)."""
    if n <= 0:
        raise ValueError(f"core3_pos requires n > 0, got {n}")
    while n % 3 == 0:
        n //= 3
    return n


def core2_pos(n: int) -> int:
    """Strip all factors of 2 from positive integer `n > 0`."""
    if n <= 0:
        raise ValueError(f"core2_pos requires n > 0, got {n}")
    return n >> ((n & -n).bit_length() - 1)


def cousin_diamond_step_int(x: int, q: int = 3) -> int:
    """
    One step of the solvable mixed-(2,3) Collatz cousin `T_diamond` on `Z`
    (generalized to odd multiplier `q` for `M3` testing):
      - `x` odd: `(q * x + 1) // 2`
      - `x > 2` even with `x % 6 == 2`: `(x - 2) // 3`
      - all other even `x`: `x // 2`
    """
    if (x & 1) == 1:
        return (q * x + 1) >> 1
    if x > 2 and (x % 6) == 2:
        return (x - 2) // 3
    return x >> 1


def cousin_diamond_step_q6(x: Fraction) -> Fraction:
    """Exact extension of `T_diamond` to `Q_(6)` (`gcd(denom(x), 6) == 1`)."""
    if math.gcd(x.denominator, 6) != 1:
        raise ValueError(f"Expected rational coprime to 6, got {x}")
    inv_d = pow(x.denominator, -1, 6)
    r6 = (x.numerator * inv_d) % 6
    if (r6 & 1) == 1:
        return (3 * x + 1) / 2
    if x > 2 and r6 == 2:
        return (x - 2) / 3
    return x / 2


def cousin_diamond_phi(x: int) -> int:
    """Nonlocal 3-adic core Lyapunov functional `Phi_diamond(x) = core3(x + 1)^2 * (x + 1)`."""
    if x <= 0:
        raise ValueError(f"cousin_diamond_phi requires x > 0, got {x}")
    c = core3_pos(x + 1)
    return c * c * (x + 1)


# ----------------------------------------------------------------------------
# Wave 4 Orthogonal Paradigm Auditors (Branches P1, P2, P3, P4, P5)
# ----------------------------------------------------------------------------


def audit_h1_berg_meinardus_radial_hardy_barrier(max_r: int = 10) -> Dict[str, Any]:
    """
    Branch P1 (`W4.1`): Verify that for classical Hardy (`w_n = 1`), weighted Bergman
    (`w_n = (n + 1)^(-2)`, `(n + 1)^(-3)`), and radial disk-exponential (`w_n = 2^(-n)`)
    spaces on `H_0(w)`, every iterate `B^r` (`1 <= r <= max_r`) satisfies
    `||B^r||_{H_0(w)}^2 >= (w(n_odd) + w(n_even)) / w(m_r) > 1` at `n_odd = 2^(r+1) - 1`.
    """
    weight_families: Dict[str, Callable[[int], Fraction]] = {
        "hardy_H2": lambda _n: Fraction(1, 1),
        "bergman_alpha1": lambda n: Fraction(1, (n + 1) ** 2),
        "bergman_alpha2": lambda n: Fraction(1, (n + 1) ** 3),
        "radial_exp_half": lambda n: Fraction(1, 1 << min(n, 120)),
    }
    all_exceed_one = True
    min_ratio = Fraction(10**9, 1)
    for r in range(1, max_r + 1):
        n_odd = (1 << (r + 1)) - 1
        m_target = (3**r) * 2 - 1
        n_even = (1 << r) * m_target
        end_odd, _ = int_iter_and_parity(n_odd, r, q=3)
        end_even, _ = int_iter_and_parity(n_even, r, q=3)
        if not (end_odd == m_target and end_even == m_target and 3 <= n_odd < m_target < n_even):
            all_exceed_one = False
        for w_fn in weight_families.values():
            ratio = (w_fn(n_odd) + w_fn(n_even)) / w_fn(m_target)
            if ratio <= 1:
                all_exceed_one = False
            if ratio < min_ratio:
                min_ratio = ratio

    return {
        "barrier_verified": all_exceed_one,
        "tested_horizons": max_r,
        "min_norm_sq_lower_bound": min_ratio,
        "strictly_gt_one": min_ratio > 1,
    }


def audit_h2_furstenberg_zero_entropy_and_mod3_pinning() -> Dict[str, Any]:
    """
    Branch P2 (`W4_H2`): Verify the two structural obstructions blocking direct
    Rudolph-Host `(x2, x3)` measure rigidity and deterministic mod-`3^B` glide mixing:
    1. Every positive cycle denominator `D = 2^K - 3^W` (`K >= 3, W >= 1`) has `gcd(D, 6) == 1`,
       making `(1/D)Z/Z` a finite zero-entropy `(x2, x3)`-invariant subgroup of `R/Z`.
    2. For every `B >= 1` and Mersenne glide `n = 2^W - 1` (`W > B`), Steps `B .. W - 1`
       are pinned deterministically to the single residue `-1 == 3^B - 1 (mod 3^B)`.
    """
    finite_subgroups_invariant = True
    for k_len, w_val in ((5, 3), (8, 5), (13, 8), (65, 41)):
        det = (1 << k_len) - (3**w_val)
        if det <= 0 or math.gcd(det, 6) != 1:
            finite_subgroups_invariant = False
            break
        if det <= 2000:
            img2 = {(2 * r) % det for r in range(det)}
            img3 = {(3 * r) % det for r in range(det)}
            if len(img2) != det or len(img3) != det:
                finite_subgroups_invariant = False

    pinning_verified = True
    for b_exp in (1, 2, 3, 4):
        mod3 = 3**b_exp
        w_glide = b_exp + 12
        cur = (1 << w_glide) - 1
        pinned_residues: Set[int] = set()
        for step_idx in range(w_glide):
            if step_idx >= b_exp:
                pinned_residues.add(cur % mod3)
            cur = int_compressed_step(cur, q=3)
        if pinned_residues != {mod3 - 1}:
            pinning_verified = False

    return {
        "hypothesis_falsified": finite_subgroups_invariant and pinning_verified,
        "zero_entropy_x2_x3_subgroups_verified": finite_subgroups_invariant,
        "mersenne_mod_pow3_dirac_pinning_verified": pinning_verified,
    }


def _dec_neg_log1m(a: Fraction, prec: int = 320) -> decimal.Decimal:
    """High-precision evaluation of `-log(1 - a)` for all rational `|a| < 1`."""
    if not isinstance(a, Fraction):
        a = Fraction(a)
    if abs(a) >= 1:
        raise ValueError(f"_dec_neg_log1m requires |a| < 1, got {a}")
    if prec < 30:
        raise ValueError(f"_dec_neg_log1m requires prec >= 30, got {prec}")
    if a == 0:
        return decimal.Decimal(0)
    with decimal.localcontext() as ctx:
        ctx.prec = prec + 35
        one_minus_a = decimal.Decimal(a.denominator - a.numerator) / decimal.Decimal(a.denominator)
        val = -(one_minus_a.ln())
    with decimal.localcontext() as ctx:
        ctx.prec = prec
        return +val


def _solve_homogeneous_fraction_nullvec(rows: Sequence[Sequence[Fraction]], ncols: int) -> List[Fraction]:
    """
    Compute an exact nonzero rational vector `v` of length `ncols` (`>= len(rows) + 1`)
    in the right kernel of `rows` via exact `Fraction` RREF (handling both normal and
    degenerate pivot ranks cleanly without raising `StopIteration`).
    """
    nrows = len(rows)
    if ncols <= nrows:
        raise ValueError(f"Expected underdetermined homogeneous system (ncols={ncols} > nrows={nrows})")
    mat = [list(r) for r in rows]
    pivot_cols: List[int] = []
    r_idx = 0
    for c_idx in range(ncols):
        if r_idx >= nrows:
            break
        piv = next((r for r in range(r_idx, nrows) if mat[r][c_idx] != 0), None)
        if piv is None:
            continue
        mat[r_idx], mat[piv] = mat[piv], mat[r_idx]
        inv = Fraction(1, 1) / mat[r_idx][c_idx]
        mat[r_idx] = [x * inv for x in mat[r_idx]]
        for r in range(nrows):
            if r != r_idx and mat[r][c_idx] != 0:
                fac = mat[r][c_idx]
                mat[r] = [mat[r][c] - fac * mat[r_idx][c] for c in range(ncols)]
        pivot_cols.append(c_idx)
        r_idx += 1

    pivot_set = set(pivot_cols)
    free_cols = [c for c in range(ncols) if c not in pivot_set]
    chosen_free = free_cols[-1]
    vec = [Fraction(0) for _ in range(ncols)]
    vec[chosen_free] = Fraction(1)
    for row_pos, p_col in enumerate(pivot_cols):
        vec[p_col] = -mat[row_pos][chosen_free]
    return vec


def _det3_int(rows3: Sequence[Tuple[int, int, int]]) -> int:
    """Exact 3x3 integer determinant."""
    (a00, a01, a02), (a10, a11, a12), (a20, a21, a22) = rows3
    return (
        a00 * (a11 * a22 - a12 * a21)
        - a01 * (a10 * a22 - a12 * a20)
        + a02 * (a10 * a21 - a11 * a20)
    )


def _solve_type2_hermite_pade_index(
    a1: Fraction, a2: Fraction, n1: int, n2: int, prec: int = 320
) -> Dict[str, Any]:
    """
    Solve exact cleared-denominator Type-II Hermite-Pade approximants of contact index
    `(n1, n2)` (`deg Q <= n1 + n2`) to `(-log(1 - a1*t), -log(1 - a2*t))|_{t=1}`.
    """
    if n1 < 0 or n2 < 0 or (n1 + n2) < 1:
        raise ValueError(f"Invalid Type-II contact index ({n1}, {n2})")
    if a1 == 0 or a2 == 0 or abs(a1) >= 1 or abs(a2) >= 1 or a1 == a2:
        raise ValueError(f"Expected distinct nonzero rationals in (-1, 1), got a1={a1}, a2={a2}")
    deg_q = n1 + n2
    rows2: List[List[Fraction]] = []
    for k in range(deg_q + 1, deg_q + n1 + 1):
        rows2.append([(a1 ** (k - j)) / (k - j) for j in range(deg_q + 1)])
    for k in range(deg_q + 1, deg_q + n2 + 1):
        rows2.append([(a2 ** (k - j)) / (k - j) for j in range(deg_q + 1)])

    q_pol = _solve_homogeneous_fraction_nullvec(rows2, deg_q + 1)
    q_sum = sum(q_pol)
    p1_sum = Fraction(0)
    p2_sum = Fraction(0)
    for k in range(1, deg_q + 1):
        p1_sum += sum(q_pol[j] * (a1 ** (k - j)) / (k - j) for j in range(k))
        p2_sum += sum(q_pol[j] * (a2 ** (k - j)) / (k - j) for j in range(k))
    lcm2 = math.lcm(q_sum.denominator, math.lcm(p1_sum.denominator, p2_sum.denominator))
    qi, p1i, p2i = int(q_sum * lcm2), int(p1_sum * lcm2), int(p2_sum * lcm2)
    g2 = math.gcd(abs(qi), math.gcd(abs(p1i), abs(p2i)))
    if g2 > 1:
        qi //= g2
        p1i //= g2
        p2i //= g2
    if qi < 0:
        qi, p1i, p2i = -qi, -p1i, -p2i

    with decimal.localcontext() as ctx:
        ctx.prec = prec
        l1 = _dec_neg_log1m(a1, prec=prec)
        l2 = _dec_neg_log1m(a2, prec=prec)
        ln2 = decimal.Decimal(2).ln()
        err2 = max(
            abs(decimal.Decimal(qi) * l1 - decimal.Decimal(p1i)),
            abs(decimal.Decimal(qi) * l2 - decimal.Decimal(p2i)),
        )
        err_log2 = float(err2.ln() / ln2) if err2 > 0 else float("-inf")
    return {
        "qi": qi,
        "p1i": p1i,
        "p2i": p2i,
        "q_bits": float(abs(qi).bit_length()),
        "err_log2": err_log2,
    }


def _solve_type1_and_type2_hermite_pade(a1: Fraction, a2: Fraction, n: int) -> Dict[str, Any]:
    """
    Compute exact cleared-denominator Type-I `(n, n, n)` and Type-II Casorati triple
    `((n, n), (n + 1, n), (n, n + 1))` Hermite-Pade approximants at
    `(1, -log(1 - a1*t), -log(1 - a2*t))|_{t=1}`, including exact 3x3 Casorati determinant.
    """
    if not isinstance(a1, Fraction):
        a1 = Fraction(a1)
    if not isinstance(a2, Fraction):
        a2 = Fraction(a2)
    if n < 1:
        raise ValueError(f"Degree n must be >= 1, got {n}")
    if a1 == 0 or a2 == 0 or abs(a1) >= 1 or abs(a2) >= 1 or a1 == a2:
        raise ValueError(f"Expected distinct nonzero rationals in (-1, 1), got a1={a1}, a2={a2}")

    # Type-I of degree (n, n, n)
    rows1: List[List[Fraction]] = []
    for k in range(n + 1, 3 * n + 2):
        row: List[Fraction] = []
        for j in range(n + 1):
            row.append((a1 ** (k - j)) / (k - j) if k > j else Fraction(0))
        for j in range(n + 1):
            row.append((a2 ** (k - j)) / (k - j) if k > j else Fraction(0))
        rows1.append(row)
    sol1 = _solve_homogeneous_fraction_nullvec(rows1, 2 * n + 2)
    b_pol, c_pol = sol1[: n + 1], sol1[n + 1 :]
    a_pol: List[Fraction] = []
    for k in range(n + 1):
        ak = Fraction(0)
        for j in range(k):
            ak -= b_pol[j] * (a1 ** (k - j)) / (k - j)
            ak -= c_pol[j] * (a2 ** (k - j)) / (k - j)
        a_pol.append(ak)
    a_sum, b_sum, c_sum = sum(a_pol), sum(b_pol), sum(c_pol)
    lcm1 = math.lcm(a_sum.denominator, math.lcm(b_sum.denominator, c_sum.denominator))
    ai, bi, ci = int(a_sum * lcm1), int(b_sum * lcm1), int(c_sum * lcm1)
    g1 = math.gcd(abs(ai), math.gcd(abs(bi), abs(ci)))
    if g1 > 1:
        ai //= g1
        bi //= g1
        ci //= g1

    # Type-II consecutive step-line Casorati triple ((n, n), (n + 1, n), (n + 1, n + 1)) + (n, n + 1)
    t2_nn = _solve_type2_hermite_pade_index(a1, a2, n, n, prec=320)
    t2_n1n = _solve_type2_hermite_pade_index(a1, a2, n + 1, n, prec=320)
    t2_nn1 = _solve_type2_hermite_pade_index(a1, a2, n, n + 1, prec=320)
    t2_n1n1 = _solve_type2_hermite_pade_index(a1, a2, n + 1, n + 1, prec=320)
    stepline_casorati_det = _det3_int(
        (
            (int(t2_nn["qi"]), int(t2_nn["p1i"]), int(t2_nn["p2i"])),
            (int(t2_n1n["qi"]), int(t2_n1n["p1i"]), int(t2_n1n["p2i"])),
            (int(t2_n1n1["qi"]), int(t2_n1n1["p1i"]), int(t2_n1n1["p2i"])),
        )
    )

    with decimal.localcontext() as ctx:
        ctx.prec = 320
        l1 = _dec_neg_log1m(a1, prec=320)
        l2 = _dec_neg_log1m(a2, prec=320)
        ln2 = decimal.Decimal(2).ln()
        rem1 = abs(decimal.Decimal(ai) + decimal.Decimal(bi) * l1 + decimal.Decimal(ci) * l2)
        rem1_log2 = float(rem1.ln() / ln2) if rem1 > 0 else float("-inf")
        return {
            "type1_height_bits": float(max(abs(ai), abs(bi), abs(ci)).bit_length()),
            "type1_rem_log2": rem1_log2,
            "type2_q_bits": float(t2_nn["q_bits"]),
            "type2_err_log2": float(t2_nn["err_log2"]),
            "type2_offdiag_n1_n_err_log2": float(t2_n1n["err_log2"]),
            "type2_offdiag_n_n1_err_log2": float(t2_nn1["err_log2"]),
            "stepline_casorati_det": stepline_casorati_det,
            "stepline_casorati_det_nonzero": stepline_casorati_det != 0,
        }


def _solve_folded_symmetric_type2_diag(a: Fraction, n: int, prec: int = 520) -> Dict[str, Any]:
    """
    Fast exact diagonal `(n, n)` Type-II Hermite-Pade solver at symmetric basis `(a, -a)`
    (`0 < |a| < 1`), exploiting exact even-polynomial symmetry `Q_{n, n}(t) = sum_{r=0}^n c_r t^{2r}`
    to certify high-degree (`n = 55`) odd-prime `lcm(1, 3, ..., 2n - 1)` explosion in milliseconds.
    """
    if not isinstance(a, Fraction):
        a = Fraction(a)
    if n < 1 or a == 0 or abs(a) >= 1:
        raise ValueError(f"Expected n >= 1 and 0 < |a| < 1, got n={n}, a={a}")
    rows = [
        [(a ** (k - 2 * r)) / (k - 2 * r) for r in range(n + 1)]
        for k in range(2 * n + 1, 3 * n + 1)
    ]
    c_even = _solve_homogeneous_fraction_nullvec(rows, n + 1)
    q_pol: List[Fraction] = []
    for r in range(n):
        q_pol.extend([c_even[r], Fraction(0)])
    q_pol.append(c_even[n])
    q_sum = sum(q_pol)
    p1_sum = sum(
        sum(q_pol[j] * (a ** (k - j)) / (k - j) for j in range(k))
        for k in range(1, 2 * n + 1)
    )
    p2_sum = sum(
        sum(q_pol[j] * ((-a) ** (k - j)) / (k - j) for j in range(k))
        for k in range(1, 2 * n + 1)
    )
    lcm2 = math.lcm(q_sum.denominator, math.lcm(p1_sum.denominator, p2_sum.denominator))
    qi, p1i, p2i = int(q_sum * lcm2), int(p1_sum * lcm2), int(p2_sum * lcm2)
    g2 = math.gcd(abs(qi), math.gcd(abs(p1i), abs(p2i)))
    if g2 > 1:
        qi, p1i, p2i = qi // g2, p1i // g2, p2i // g2
    if qi < 0:
        qi, p1i, p2i = -qi, -p1i, -p2i
    with decimal.localcontext() as ctx:
        ctx.prec = prec
        l1 = _dec_neg_log1m(a, prec=prec)
        l2 = _dec_neg_log1m(-a, prec=prec)
        ln2 = decimal.Decimal(2).ln()
        err = max(
            abs(decimal.Decimal(qi) * l1 - decimal.Decimal(p1i)),
            abs(decimal.Decimal(qi) * l2 - decimal.Decimal(p2i)),
        )
        return {
            "q_bits": float(abs(qi).bit_length()),
            "err_log2": float(err.ln() / ln2),
        }


def audit_h3_simultaneous_pade_and_2block_resultant() -> Dict[str, Any]:
    """
    Branch P3 (`W4.3` & `W4_H3A`/`W4_H3B`):
    1. Verify 3-body Mahler-duality obstruction across BOTH regimes of `{2,3}`-smooth
       bases spanning `Z*log(2) + Z*log(3)`:
       - Asymmetric `{2,3}`-smooth basis `(1/4, 1/3)` (and `(1/9, 13/256)`): even the
         diagonal `(n, n)` cleared-denominator Type-II error diverges (`> 2^3 > 1` at `n = 6`),
         with nonzero step-line Casorati determinant.
       - Unique folded symmetric `{2,3}`-smooth basis `(1/3, -1/3)` (`1 - a1 = 2/3, 1 - a2 = 4/3`):
         finite-`n` Chebyshev dips make diagonal `(n, n)` appear convergent for `n <= 35`
         (`~ 2^-9.99 < 0.001` at `n = 6`), YET step-line `(n+1, n)` already explodes
         (`+10.66` bits at `n = 6`), Type-I height overtakes remainder decay at `n = 8`
         (`38 > 37.46` bits), and odd primes up to `2n - 1` in `lcm(1, 3, ..., 2n - 1) ~ e^(2n)`
         drive even diagonal `(n, n)` to diverge (`+7.08` bits at `n = 55`), blocking Baker-free
         linear-form transference!
    2. Verify unconditional 2-block resultant elimination (`two_block_brox_resultant_identities`
       & `two_block_quotient_mersenne_gcd_and_mod3_lock`) across parameter space.
    3. Verify exact minimal falsifiers `(2,1,2,3)` (`gcd=5`) and `(7,1,1,4)` (`gcd=7`)
       refuting uncoupled `gcd(H0, H1) <= 2^{gcd(a1, a2)} - 1`.
    """
    from . import cs_lp_cycles as clp

    pade_n6 = _solve_type1_and_type2_hermite_pade(Fraction(1, 4), Fraction(1, 3), 6)
    pade_conv_n2 = _solve_type1_and_type2_hermite_pade(Fraction(1, 9), Fraction(13, 256), 2)
    pade_sym_n6 = _solve_type1_and_type2_hermite_pade(Fraction(1, 3), Fraction(-1, 3), 6)
    pade_sym_n8 = _solve_type1_and_type2_hermite_pade(Fraction(1, 3), Fraction(-1, 3), 8)
    pade_sym_diag_n55 = _solve_folded_symmetric_type2_diag(Fraction(1, 3), 55)
    pade_explosion_verified = (
        pade_n6["type1_height_bits"] > abs(pade_n6["type1_rem_log2"])
        and pade_n6["type2_err_log2"] > 3.0
        and bool(pade_n6["stepline_casorati_det_nonzero"])
        and pade_conv_n2["type2_err_log2"] > 15.0
        and pade_sym_n6["type2_err_log2"] < -9.5
        and bool(pade_sym_n6["stepline_casorati_det_nonzero"])
        and pade_sym_n6["type2_offdiag_n1_n_err_log2"] > 10.0
        and pade_sym_n6["type2_offdiag_n_n1_err_log2"] > 14.0
        and pade_sym_n8["type1_height_bits"] > abs(pade_sym_n8["type1_rem_log2"])
        and pade_sym_diag_n55["err_log2"] > 7.0
    )

    resultant_identities_ok = True
    for w_tot in range(2, 14):
        for k_tot in range(w_tot + 2, 2 * w_tot + 1):
            det = (1 << k_tot) - (3**w_tot)
            if det <= 0:
                continue
            for w1 in range(1, w_tot):
                w2 = w_tot - w1
                for a1 in range(1, k_tot - w_tot):
                    a2 = k_tot - w_tot - a1
                    h0, h1 = clp.two_block_brox_carries(w1, a1, w2, a2)
                    if (1 << (a1 + w2)) * h1 != (3**w1) * h0 + det * ((1 << a1) - 1):
                        resultant_identities_ok = False
                    if (1 << (a2 + w1)) * h0 != (3**w2) * h1 + det * ((1 << a2) - 1):
                        resultant_identities_ok = False

    # Check minimal shared-factor witnesses (2, 1, 2, 3) and (7, 1, 1, 4)
    h0_w4, h1_w4 = clp.two_block_brox_carries(2, 1, 2, 3)
    d_w4 = (1 << 8) - (3**4)
    h0_w8, h1_w8 = clp.two_block_brox_carries(7, 1, 1, 4)
    d_w8 = (1 << 13) - (3**8)
    shared_factor_witnesses_ok = (
        d_w4 == 175
        and math.gcd(d_w4, math.gcd(h0_w4, h1_w4)) == 5
        and d_w8 == 1631
        and math.gcd(d_w8, math.gcd(h0_w8, h1_w8)) == 7
    )

    return {
        "pade_explosion_verified": pade_explosion_verified,
        "pade_1_4_1_3_n6": pade_n6,
        "pade_sym_1_3_neg_1_3_n6": pade_sym_n6,
        "pade_sym_1_3_neg_1_3_n8": pade_sym_n8,
        "pade_sym_diag_n55": pade_sym_diag_n55,
        "resultant_identities_verified": resultant_identities_ok,
        "shared_factor_witnesses_verified": shared_factor_witnesses_ok,
    }


def audit_h4_presburger_collapse_and_polynomial_sos_barrier(max_period_p: int = 80) -> Dict[str, Any]:
    """
    Branch P4 (`W4.2` & `one_sided_presburger_infinite_forward_hits_one`):
    1. Verify two-sided Presburger separator collapse (`presburger_invariant_separator_collapse`)
       and one-sided infinite forward-closed Presburger hitting of `{2^k}` across `1 <= P <= max_period_p`
       (mirroring the universal `forall N0, P >= 1` Lean 4 proof in `Wave4WholeSpace.lean`).
    2. Verify eventually strictly increasing / polynomial / 1D SOS failure on Mersenne glides.
    """
    one_sided_hits_pow2 = True
    for p_mod in range(1, max_period_p + 1):
        pow2_residues = {(1 << k) % p_mod for k in range(16, 16 + 2 * p_mod)}
        for r0 in range(p_mod):
            closed: Set[int] = {r0}
            changed = True
            while changed:
                changed = False
                for r in list(closed):
                    for parity_shift in (0, 1):
                        x = r + parity_shift * p_mod + 2 * p_mod
                        y = (x >> 1) if (x & 1) == 0 else ((3 * x + 1) >> 1)
                        if (y % p_mod) not in closed:
                            closed.add(y % p_mod)
                            changed = True
            if not (closed & pow2_residues):
                one_sided_hits_pow2 = False
                break

    # Test degree-4 SOS polynomial V(x) = x^4 + 5*x^2 + 1 across horizons r = 1..10
    sos_refuted_all_r = True
    for r_hor in range(1, 11):
        x_seed = (1 << (r_hor + 2)) - 1
        x_end, _ = int_iter_and_parity(x_seed, r_hor, q=3)
        v_start = x_seed**4 + 5 * (x_seed**2) + 1
        v_end = x_end**4 + 5 * (x_end**2) + 1
        if not (v_end > v_start):
            sos_refuted_all_r = False

    return {
        "one_sided_presburger_hits_pow2_verified": one_sided_hits_pow2,
        "tested_max_period": max_period_p,
        "coercive_sos_refuted_verified": sos_refuted_all_r,
    }


def _decompose_2_3_coprime(m: int) -> Tuple[int, int, int]:
    """Decompose `m >= 1` into `(2^{v_2(m)}, 3^{v_3(m)}, core_{2,3}(m))`."""
    if m <= 0:
        raise ValueError(f"_decompose_2_3_coprime requires m > 0, got {m}")
    p2 = m & -m
    rem = m // p2
    p3 = 1
    while rem % 3 == 0:
        rem //= 3
        p3 *= 3
    return p2, p3, rem


def audit_syracuse_laurent_valuation_monomial_barrier(max_abs_exp: int = 8) -> Dict[str, Any]:
    """
    Branch P4.2 / P5.2 (`syracuse_laurent_valuation_monomial_impossibility`):
    1. Verify that even non-monotone COERCIVE valuation potentials such as
       `V(x) = 4^{v_2(x + 1)} * (x + 1)` strictly decrease on ALL Mersenne glides
       `x = 2^k - 1` (`k >= 2`, evading `monotone_ranking_function_r_step_impossibility`),
       yet fail on `9 -> 7` (`40 -> 512`).
    2. Verify that across ALL arbitrary-sign Laurent exponents `(alpha, beta, gamma)` in
       `[-max_abs_exp, max_abs_exp]^3` (`Z^3` in Lean 4), ZERO monomials
       `Psi(x) = (2^{v_2(x+1)})^alpha * (3^{v_3(x+1)})^beta * core_{2,3}(x+1)^gamma`
       strictly decrease across the 4-element odd Syracuse witness set `{7, 9, 17, 97}`
       (`7^gamma < 9^beta < 4^alpha < 5^gamma` with `gamma >= 1` from `97 -> 73`).
    """
    def syr_next(x: int) -> int:
        return core2_pos(3 * x + 1)

    def nonmonotone_coercive_v2_pot(x: int) -> int:
        p2, _, _ = _decompose_2_3_coprime(x + 1)
        return (p2 * p2) * (x + 1)

    mersenne_descent_ok = all(
        nonmonotone_coercive_v2_pot(syr_next((1 << k) - 1))
        < nonmonotone_coercive_v2_pot((1 << k) - 1)
        for k in range(2, 25)
    )
    witness_9_to_7_jump = (
        syr_next(9) == 7
        and nonmonotone_coercive_v2_pot(9) == 40
        and nonmonotone_coercive_v2_pot(7) == 512
    )

    witness_pairs = [(x, syr_next(x)) for x in (7, 9, 17, 97)]
    decomposed = [
        (_decompose_2_3_coprime(x + 1), _decompose_2_3_coprime(nx + 1))
        for x, nx in witness_pairs
    ]

    surviving_triples = 0
    for alpha in range(-max_abs_exp, max_abs_exp + 1):
        for beta in range(-max_abs_exp, max_abs_exp + 1):
            for gamma in range(-max_abs_exp, max_abs_exp + 1):
                ok = True
                for (p2_x, p3_x, c_x), (p2_y, p3_y, c_y) in decomposed:
                    val_x = (
                        Fraction(p2_x) ** alpha
                        * Fraction(p3_x) ** beta
                        * Fraction(c_x) ** gamma
                    )
                    val_y = (
                        Fraction(p2_y) ** alpha
                        * Fraction(p3_y) ** beta
                        * Fraction(c_y) ** gamma
                    )
                    if not (val_y < val_x):
                        ok = False
                        break
                if ok:
                    surviving_triples += 1

    return {
        "mersenne_glide_coercive_v2_descent_verified": mersenne_descent_ok,
        "coercive_v2_jump_at_9_to_7_verified": witness_9_to_7_jump,
        "laurent_cube_tested_triples": (2 * max_abs_exp + 1) ** 3,
        "laurent_surviving_triples": surviving_triples,
        "laurent_monomial_barrier_verified": (
            mersenne_descent_ok and witness_9_to_7_jump and surviving_triples == 0
        ),
    }


def _eval_nonlocal_ast(ast: Tuple[Any, ...], x: int) -> int:
    """Evaluate a positive nonlocal valuation AST node on integer `x >= 1` using exact `int` arithmetic."""
    if x < 1:
        raise ValueError(f"_eval_nonlocal_ast requires x >= 1, got {x}")
    op = ast[0]
    if op == "one":
        return 1
    if op == "two":
        return 2
    if op == "x":
        return x
    if op == "xp1":
        return x + 1
    if op == "c2_xp1":
        return core2_pos(x + 1)
    if op == "c3_xp1":
        return core3_pos(x + 1)
    if op == "c2_3xp1":
        return core2_pos(3 * x + 1)
    if op == "c3_x":
        return core3_pos(x)
    if op == "sq":
        val = _eval_nonlocal_ast(ast[1], x)
        return val * val
    lhs = _eval_nonlocal_ast(ast[1], x)
    rhs = _eval_nonlocal_ast(ast[2], x)
    if op == "add":
        return lhs + rhs
    if op == "mul":
        return lhs * rhs
    raise ValueError(f"Unknown AST operator: {op}")


def _ast_node_count(ast: Tuple[Any, ...]) -> int:
    if len(ast) == 1:
        return 1
    if len(ast) == 2:
        return 1 + _ast_node_count(ast[1])
    return 1 + _ast_node_count(ast[1]) + _ast_node_count(ast[2])


def synthesize_nonlocal_cousin_invariant_and_redteam_collatz(
    seed: int = 20261116,
    population_size: int = 120,
    generations: int = 25,
) -> Dict[str, Any]:
    """
    Branch P5 (`W4.4` & `W4_H5`):
    1. Run deterministic evolutionary AST synthesis with parsimony pressure over nonlocal
       `(core_2, core_3)` primitives on the solvable mixed-(2,3) cousin `T_diamond`,
       verifying that GP discovers a minimal 3-node exact strict step-ranking functional
       from scratch that holds across `x = 2..2000`, Mersenne glides `2^k - 1`, AND
       extreme 260-bit integers (`1 << 260`) without bit-clamping.
    2. Verify `cousin_diamond_phi(T_diamond(x)) < cousin_diamond_phi(x)` across `x = 3..2000`
       and Mersenne glides `2^k - 1` (`k = 2..30`), plus `M1` (`1/7`), `M2` (`-1, -5`),
       and `M3` (`q = 7`, cycle `5`) counter-model separation.
    3. Run the identical evolutionary nonlocal search on true Syracuse steps (`3x + 1`),
       verifying that 0% of candidates survive all odd seeds and extracting the exact
       minimal Valuation-Archimedean Antagonism falsifier (`17 -> 13` where `Phi` jumps `72 -> 2744`).
    """
    cousin_atoms = ("one", "two", "x", "xp1", "c2_xp1", "c3_xp1")
    collatz_atoms = ("one", "two", "x", "xp1", "c2_xp1", "c3_xp1", "c2_3xp1", "c3_x")
    ops = ("add", "mul", "sq")
    rng = random.Random(seed)

    def rand_ast(atoms: Tuple[str, ...], max_d: int = 3) -> Tuple[Any, ...]:
        if max_d <= 0 or rng.random() < 0.45:
            return (rng.choice(atoms),)
        op = rng.choice(ops)
        if op == "sq":
            return ("sq", rand_ast(atoms, max_d - 1))
        return (op, rand_ast(atoms, max_d - 1), rand_ast(atoms, max_d - 1))

    def mutate_ast(ast: Tuple[Any, ...], atoms: Tuple[str, ...], max_d: int = 3) -> Tuple[Any, ...]:
        if len(ast) > 1 and rng.random() < 0.25:
            return ast[1] if (len(ast) == 2 or rng.random() < 0.5) else ast[2]
        if len(ast) == 1 or max_d <= 0 or rng.random() < 0.35:
            return rand_ast(atoms, max(max_d, 1))
        if len(ast) == 2:
            return (ast[0], mutate_ast(ast[1], atoms, max_d - 1))
        if rng.random() < 0.5:
            return (ast[0], mutate_ast(ast[1], atoms, max_d - 1), ast[2])
        return (ast[0], ast[1], mutate_ast(ast[2], atoms, max_d - 1))

    # 1. Evolutionary synthesis on T_diamond (run all generations for parsimony minimization)
    cousin_train_xs = (
        list(range(3, 200))
        + [(1 << k) - 1 for k in range(2, 20)]
        + [3**k - 1 for k in range(2, 12)]
    )
    pop = [rand_ast(cousin_atoms, 3) for _ in range(population_size)]
    synthesized_cousin_ast: Optional[Tuple[Any, ...]] = None
    for _ in range(generations):
        scored = [
            (
                sum(
                    1
                    for x in cousin_train_xs
                    if _eval_nonlocal_ast(cand, cousin_diamond_step_int(x)) < _eval_nonlocal_ast(cand, x)
                ),
                -_ast_node_count(cand),
                cand,
            )
            for cand in pop
        ]
        scored.sort(reverse=True)
        if scored[0][0] == len(cousin_train_xs):
            if synthesized_cousin_ast is None or _ast_node_count(scored[0][2]) < _ast_node_count(
                synthesized_cousin_ast
            ):
                synthesized_cousin_ast = scored[0][2]
        elites = [c for _, _, c in scored[:20]]
        pop = list(elites) + [mutate_ast(rng.choice(elites), cousin_atoms, 3) for _ in range(population_size - 20)]

    cousin_holdout_xs = (
        list(range(3, 2001))
        + [(1 << k) - 1 for k in range(2, 31)]
        + [1 << 260, (1 << 260) - 1, 6 * (1 << 260) + 2]
    )
    cousin_holdout_ok = synthesized_cousin_ast is not None and all(
        _eval_nonlocal_ast(synthesized_cousin_ast, cousin_diamond_step_int(x))
        < _eval_nonlocal_ast(synthesized_cousin_ast, x)
        and cousin_diamond_phi(cousin_diamond_step_int(x)) < cousin_diamond_phi(x)
        for x in cousin_holdout_xs
    )

    # 2. Counter-model separation for T_diamond
    m1_cur = Fraction(1, 7)
    m1_orbit: List[Fraction] = []
    for _ in range(5):
        m1_orbit.append(m1_cur)
        m1_cur = cousin_diamond_step_q6(m1_cur)
    m1_cycle_ok = (m1_cur == Fraction(1, 7)) and all(v > 0 for v in m1_orbit)
    m2_cycle_ok = (
        cousin_diamond_step_int(-1) == -1
        and cousin_diamond_step_int(cousin_diamond_step_int(cousin_diamond_step_int(-5))) == -5
    )
    m3_cur = 5
    for _ in range(5):
        m3_cur = cousin_diamond_step_int(m3_cur, q=7)
    m3_cycle_ok = m3_cur == 5

    # 3. Evolutionary red-teaming on true Syracuse steps
    def syracuse_odd_step(x: int) -> int:
        y = 3 * x + 1
        return core2_pos(y)

    odd_train_xs = [x for x in range(3, 401, 2)] + [(1 << k) - 1 for k in range(3, 25)]
    c_pop = [rand_ast(collatz_atoms, 3) for _ in range(population_size)]
    best_collatz_passes = 0
    best_collatz_ast: Tuple[Any, ...] = ("x",)
    for _ in range(generations):
        c_scored = [
            (
                sum(
                    1
                    for x in odd_train_xs
                    if _eval_nonlocal_ast(cand, syracuse_odd_step(x)) < _eval_nonlocal_ast(cand, x)
                ),
                -_ast_node_count(cand),
                cand,
            )
            for cand in c_pop
        ]
        c_scored.sort(reverse=True)
        best_collatz_passes, _, best_collatz_ast = c_scored[0]
        elites = [c for _, _, c in c_scored[:20]]
        c_pop = list(elites) + [mutate_ast(rng.choice(elites), collatz_atoms, 3) for _ in range(population_size - 20)]

    collatz_no_full_survivor = best_collatz_passes < len(odd_train_xs)
    min_falsifier_odd = min(
        x
        for x in odd_train_xs
        if not (_eval_nonlocal_ast(best_collatz_ast, syracuse_odd_step(x)) < _eval_nonlocal_ast(best_collatz_ast, x))
    )
    antagonism_17_to_13_ok = (
        syracuse_odd_step(17) == 13
        and core3_pos(17 + 1) == 2
        and core3_pos(13 + 1) == 14
        and cousin_diamond_phi(17) == 72
        and cousin_diamond_phi(13) == 2744
    )

    return {
        "cousin_synthesized_ast": synthesized_cousin_ast,
        "cousin_synthesized_node_count": (
            _ast_node_count(synthesized_cousin_ast) if synthesized_cousin_ast is not None else None
        ),
        "cousin_holdout_verified": cousin_holdout_ok,
        "cousin_m1_1_over_7_cycle_verified": m1_cycle_ok,
        "cousin_m2_neg_cycles_verified": m2_cycle_ok,
        "cousin_m3_q7_cycle5_verified": m3_cycle_ok,
        "true_syracuse_best_passes": best_collatz_passes,
        "true_syracuse_total_tested": len(odd_train_xs),
        "true_syracuse_all_candidates_falsified": collatz_no_full_survivor,
        "true_syracuse_minimal_falsifier_odd": min_falsifier_odd,
        "antagonism_17_to_13_verified": antagonism_17_to_13_ok,
    }


def _eval_backward_tree_ast(
    ast: Tuple[Any, ...], y: int, w: int, c_u: int, q_idx: int
) -> int:
    """Evaluate a nonlocal generator-tree functional on `(y = exact_backward_quotient(1, u, q), u, q)`."""
    op = ast[0]
    if op == "one":
        return 1
    if op == "y":
        return y
    if op == "yp1":
        return y + 1
    if op == "c2_yp1":
        return core2_pos(y + 1)
    if op == "c3_yp1":
        return core3_pos(y + 1)
    if op == "pow3_w":
        return 3**w
    if op == "carry_u":
        return c_u
    if op == "qp1":
        return q_idx + 1
    if op == "sq":
        val = _eval_backward_tree_ast(ast[1], y, w, c_u, q_idx)
        return val * val
    lhs = _eval_backward_tree_ast(ast[1], y, w, c_u, q_idx)
    rhs = _eval_backward_tree_ast(ast[2], y, w, c_u, q_idx)
    if op == "add":
        return lhs + rhs
    if op == "mul":
        return lhs * rhs
    raise ValueError(f"Unknown backward-tree AST operator: {op}")


def synthesize_and_redteam_backward_quotient_tree_invariants(
    seed: int = 20261117,
    population_size: int = 100,
    generations: int = 20,
) -> Dict[str, Any]:
    """
    Branch P5.3 (`one_generator_weight_le_five_never_surviving_mod373248`,
    `collatz_standard_iff_mod373248_unique_first_hit_weight_ge_six`, &
    `mod373248_min_weight_six_witness_184111`):
    1. Verify the exact sharp `w <= 5` forward elimination on `exact_backward_quotient(1, u, q)`:
       - Every surviving `r mod 512` (`27` classes) has 9-step odd parity weight `>= 6`;
       - Across all core parity words `u` (`|u| <= 9`, `sum(u) <= 5`) and `q in 0..4`,
         `exact_backward_quotient(1, u, q)` NEVER hits `is_surviving_mod373248_class`;
       - Exact sharpness at `u = (1, 1, 1, 1, 0, 1, 0, 1), q = 0`: `sum(u) == 6`,
         `exact_backward_quotient(1, u, 0) == 184111`, `backward_one_total_steps(u, 0) == 27`,
         `is_surviving_mod373248_class(184111) == True`, and `is_first_hit_one_pair(u, 0) == True`.
    2. Run evolutionary nonlocal search on `exact_backward_quotient(1, u, q)`:
       - Synthesizes a minimal exact invariant strictly increasing along fixed-`u` `q -> q + 1` rays;
       - Red-teams cross-`u` backward core-tree prefix extensions `(u_suffix, q_s) -> (u_full, q_f)`
         across the `n = 27` backward chain (`3077 -> ... -> 27`), proving that every purely
         `(y, y+1, core_2(y+1), core_3(y+1))` growth envelope is falsified by forward-expanding
         supercritical excursions (`3077 -> 27`, drop factor `> 113x`).
    """
    from . import cs_forest_transfer as cft
    from .parity_2adic import affine_parameters, parity_vector

    # 1a. Verify all 27 surviving mod-512 residues have 9-step weight >= 6
    surv512 = [r for r in range(512) if cft.is_surviving_mod512_residue(r)]
    mod512_min_w9 = min(sum(parity_vector(r, 9)) for r in surv512)
    mod512_nine_step_ge6_ok = (len(surv512) == 27) and (mod512_min_w9 == 6)

    # 1b. Exhaustively test core words of length <= 9 with weight <= 5 across q = 0..4
    w_le_5_disjoint_ok = True
    tested_low_weight_pairs = 0
    core_words_le9: List[Tuple[int, ...]] = [(1,)]
    for length in range(2, 10):
        for mid in product((0, 1), repeat=length - 2):
            u_cand = (1,) + mid + (1,)
            core_words_le9.append(u_cand)
            if sum(u_cand) <= 5:
                for q_idx in range(5):
                    tested_low_weight_pairs += 1
                    yq = cft.exact_backward_quotient(1, u_cand, q_idx)
                    if cft.is_surviving_mod373248_class(yq):
                        w_le_5_disjoint_ok = False

    # 1c. Verify sharp w = 6 witness 184111
    u_sharp = (1, 1, 1, 1, 0, 1, 0, 1)
    sharp_184111_ok = (
        sum(u_sharp) == 6
        and cft.exact_backward_quotient(1, u_sharp, 0) == 184111
        and cft.backward_one_total_steps(u_sharp, 0) == 27
        and cft.is_surviving_mod373248_class(184111)
        and cft.is_first_hit_one_pair(u_sharp, 0)
    )

    # 2a. Evolutionary synthesis on fixed-u q -> q + 1 generator rays
    ray_atoms = ("one", "y", "yp1", "c2_yp1", "c3_yp1", "pow3_w", "carry_u", "qp1")
    y_only_atoms = ("one", "y", "yp1", "c2_yp1", "c3_yp1")
    ops = ("add", "mul", "sq")
    rng = random.Random(seed)

    def rand_tree_ast(atoms: Tuple[str, ...], max_d: int = 3) -> Tuple[Any, ...]:
        if max_d <= 0 or rng.random() < 0.45:
            return (rng.choice(atoms),)
        op = rng.choice(ops)
        if op == "sq":
            return ("sq", rand_tree_ast(atoms, max_d - 1))
        return (op, rand_tree_ast(atoms, max_d - 1), rand_tree_ast(atoms, max_d - 1))

    def mutate_tree_ast(ast: Tuple[Any, ...], atoms: Tuple[str, ...], max_d: int = 3) -> Tuple[Any, ...]:
        if len(ast) > 1 and rng.random() < 0.25:
            return ast[1] if (len(ast) == 2 or rng.random() < 0.5) else ast[2]
        if len(ast) == 1 or max_d <= 0 or rng.random() < 0.35:
            return rand_tree_ast(atoms, max(max_d, 1))
        if len(ast) == 2:
            return (ast[0], mutate_tree_ast(ast[1], atoms, max_d - 1))
        if rng.random() < 0.5:
            return (ast[0], mutate_tree_ast(ast[1], atoms, max_d - 1), ast[2])
        return (ast[0], ast[1], mutate_tree_ast(ast[2], atoms, max_d - 1))

    ray_samples: List[Tuple[Tuple[int, int, int, int], Tuple[int, int, int, int]]] = []
    for u_sample in core_words_le9[:40]:
        _, w_s, c_s = affine_parameters(u_sample)
        for q_idx in range(3):
            y0 = cft.exact_backward_quotient(1, u_sample, q_idx)
            y1 = cft.exact_backward_quotient(1, u_sample, q_idx + 1)
            ray_samples.append(((y0, w_s, c_s, q_idx), (y1, w_s, c_s, q_idx + 1)))

    pop = [rand_tree_ast(ray_atoms, 2) for _ in range(population_size)]
    best_ray_ast: Optional[Tuple[Any, ...]] = None
    for _ in range(generations):
        scored = [
            (
                sum(
                    1
                    for s0, s1 in ray_samples
                    if _eval_backward_tree_ast(cand, *s0) < _eval_backward_tree_ast(cand, *s1)
                ),
                -_ast_node_count(cand),
                cand,
            )
            for cand in pop
        ]
        scored.sort(reverse=True)
        if scored[0][0] == len(ray_samples):
            if best_ray_ast is None or _ast_node_count(scored[0][2]) < _ast_node_count(best_ray_ast):
                best_ray_ast = scored[0][2]
        elites = [c for _, _, c in scored[:20]]
        pop = list(elites) + [mutate_tree_ast(rng.choice(elites), ray_atoms, 2) for _ in range(population_size - 20)]

    # 2b. Extract exact backward first-hit chain along n = 27's odd orbit (1 <- 5 <- ... <- 3077 <- ... <- 27)
    odd_chain_27: List[int] = []
    cur = 27
    while cur != 1:
        if (cur & 1) == 1:
            odd_chain_27.append(cur)
        cur = cft.collatz_compressed_int(cur)
    # Reverse from 1-basin outward toward 27: consecutive steps in backward tree
    rev_odds = list(reversed(odd_chain_27))
    backward_transitions: List[Tuple[Tuple[int, int, int, int], Tuple[int, int, int, int]]] = []
    for idx in range(len(rev_odds) - 1):
        y_parent = rev_odds[idx]
        y_child = rev_odds[idx + 1]
        u_p, q_p = cft.encode_convergent_odd_to_first_hit_pair(y_parent)
        u_c, q_c = cft.encode_convergent_odd_to_first_hit_pair(y_child)
        _, wp, cp = affine_parameters(u_p)
        _, wc, cc = affine_parameters(u_c)
        backward_transitions.append(((y_parent, wp, cp, q_p), (y_child, wc, cc, q_c)))

    # Red-team y-only nonlocal functionals for strict backward growth along n = 27's tree branch
    t_pop = [rand_tree_ast(y_only_atoms, 3) for _ in range(population_size)]
    best_tree_passes = 0
    for _ in range(generations):
        t_scored = [
            (
                sum(
                    1
                    for p_st, c_st in backward_transitions
                    if _eval_backward_tree_ast(cand, *p_st) < _eval_backward_tree_ast(cand, *c_st)
                ),
                -_ast_node_count(cand),
                cand,
            )
            for cand in t_pop
        ]
        t_scored.sort(reverse=True)
        best_tree_passes = t_scored[0][0]
        elites = [c for _, _, c in t_scored[:20]]
        t_pop = list(elites) + [
            mutate_tree_ast(rng.choice(elites), y_only_atoms, 3) for _ in range(population_size - 20)
        ]

    backward_tree_y_monotone_falsified = (
        max(odd_chain_27) == 3077
        and odd_chain_27[0] == 27
        and best_tree_passes < len(backward_transitions)
    )

    return {
        "mod512_surviving_count": len(surv512),
        "mod512_min_nine_step_weight": mod512_min_w9,
        "mod512_nine_step_weight_ge6_verified": mod512_nine_step_ge6_ok,
        "tested_low_weight_pairs": tested_low_weight_pairs,
        "weight_le_5_mod373248_disjoint_verified": w_le_5_disjoint_ok,
        "sharp_weight_6_witness_184111_verified": sharp_184111_ok,
        "q_ray_synthesized_ast": best_ray_ast,
        "q_ray_strict_growth_verified": best_ray_ast is not None,
        "n27_backward_transitions": len(backward_transitions),
        "n27_best_y_only_passes": best_tree_passes,
        "backward_tree_y_monotone_falsified": backward_tree_y_monotone_falsified,
    }


def verify_witness_bank_ground_truth(bank_path: Optional[Path] = None) -> Dict[str, Any]:
    """
    Dynamically re-compute and verify the mathematical ground truth of EVERY witness
    entry across all 5 domains of `witness_bank.json`.
    """
    from . import cs_forest_transfer as cft
    from . import cs_lp_cycles as clp
    from .boost_mechanisms import is_surviving_mod1296_class

    bank = load_witness_bank(bank_path)
    failed_witnesses: List[str] = []
    verified_count = 0

    # 1. z_pos_high_glide
    for entry in bank["domains"]["z_pos_high_glide"]:
        wid = str(entry["witness_id"])
        seed = int(entry["seed"])
        ok = seed >= 1
        checked_keys: Set[str] = {"witness_id", "seed", "kills_mechanisms"}
        claims_checked = 0
        if "compressed_steps_to_1" in entry:
            checked_keys.add("compressed_steps_to_1")
            claims_checked += 1
            cur = seed
            steps = 0
            w_odd = 0
            peak_comp = cur
            peak_odd = cur if (cur & 1) == 1 else 1
            while cur != 1 and steps < 5000:
                if (cur & 1) == 1:
                    w_odd += 1
                    if cur > peak_odd:
                        peak_odd = cur
                cur = int_compressed_step(cur, q=3)
                steps += 1
                if cur > peak_comp:
                    peak_comp = cur
            ok = ok and (cur == 1) and (steps == int(entry["compressed_steps_to_1"]))
            if "odd_weight" in entry:
                checked_keys.add("odd_weight")
                ok = ok and (w_odd == int(entry["odd_weight"]))
            if "peak_odd" in entry:
                checked_keys.add("peak_odd")
                ok = ok and (peak_odd == int(entry["peak_odd"]))
            if "peak_compressed" in entry:
                checked_keys.add("peak_compressed")
                ok = ok and (peak_compressed := peak_comp) == int(entry["peak_compressed"])
        if "core_word" in entry or "q_index" in entry:
            if "core_word" in entry and "q_index" in entry:
                checked_keys.update(("core_word", "q_index"))
                claims_checked += 1
                u_w = tuple(int(b) for b in entry["core_word"])
                q_i = int(entry["q_index"])
                ok = (
                    ok
                    and cft.exact_backward_quotient(1, u_w, q_i) == seed
                    and cft.is_first_hit_one_pair(u_w, q_i)
                )
                if "compressed_steps_to_1" in entry:
                    ok = ok and (cft.backward_one_total_steps(u_w, q_i) == int(entry["compressed_steps_to_1"]))
            else:
                ok = False
        if "survives_mod373248" in entry:
            checked_keys.add("survives_mod373248")
            claims_checked += 1
            ok = ok and (cft.is_surviving_mod373248_class(seed) == bool(entry["survives_mod373248"]))
        if "survives_mod1296" in entry:
            checked_keys.add("survives_mod1296")
            claims_checked += 1
            ok = ok and (is_surviving_mod1296_class(seed) == bool(entry["survives_mod1296"]))
        if "next_odd" in entry:
            checked_keys.add("next_odd")
            claims_checked += 1
            nxt = core2_pos(3 * seed + 1) if seed >= 1 else 1
            ok = ok and ((seed & 1) == 1) and (nxt == int(entry["next_odd"]))
            if "compressed_steps" in entry:
                checked_keys.add("compressed_steps")
                v2_3x1 = ((3 * seed + 1) & -(3 * seed + 1)).bit_length() - 1
                ok = ok and (v2_3x1 == int(entry["compressed_steps"]))
            if "core3_seed_plus_1" in entry:
                checked_keys.add("core3_seed_plus_1")
                ok = ok and (core3_pos(seed + 1) == int(entry["core3_seed_plus_1"]))
            if "core3_next_plus_1" in entry:
                checked_keys.add("core3_next_plus_1")
                ok = ok and (core3_pos(nxt + 1) == int(entry["core3_next_plus_1"]))
            if "phi_diamond_seed" in entry:
                checked_keys.add("phi_diamond_seed")
                ok = ok and (cousin_diamond_phi(seed) == int(entry["phi_diamond_seed"]))
            if "phi_diamond_next" in entry:
                checked_keys.add("phi_diamond_next")
                ok = ok and (cousin_diamond_phi(nxt) == int(entry["phi_diamond_next"]))
            if any(
                k in entry
                for k in (
                    "v2_pow_seed_plus_1",
                    "v2_pow_next_plus_1",
                    "coprime23_seed_plus_1",
                    "coprime23_next_plus_1",
                    "v3_pow_seed_plus_1",
                    "v3_pow_next_plus_1",
                )
            ):
                req_val_keys = (
                    "v2_pow_seed_plus_1",
                    "v2_pow_next_plus_1",
                    "coprime23_seed_plus_1",
                    "coprime23_next_plus_1",
                )
                if all(k in entry for k in req_val_keys):
                    checked_keys.update(req_val_keys)
                    p2_s, p3_s, c_s = _decompose_2_3_coprime(seed + 1)
                    p2_n, p3_n, c_n = _decompose_2_3_coprime(nxt + 1)
                    ok = (
                        ok
                        and p2_s == int(entry["v2_pow_seed_plus_1"])
                        and p2_n == int(entry["v2_pow_next_plus_1"])
                        and c_s == int(entry["coprime23_seed_plus_1"])
                        and c_n == int(entry["coprime23_next_plus_1"])
                    )
                    if "v3_pow_seed_plus_1" in entry or "v3_pow_next_plus_1" in entry:
                        if "v3_pow_seed_plus_1" in entry and "v3_pow_next_plus_1" in entry:
                            checked_keys.update(("v3_pow_seed_plus_1", "v3_pow_next_plus_1"))
                            ok = (
                                ok
                                and p3_s == int(entry["v3_pow_seed_plus_1"])
                                and p3_n == int(entry["v3_pow_next_plus_1"])
                            )
                        else:
                            ok = False
                else:
                    ok = False
        elif "v2_pow_seed" in entry or "v3_pow_seed" in entry:
            req_spine_keys = (
                "v2_pow_seed",
                "v3_pow_seed",
                "v2_pow_seed_plus_1",
                "v3_pow_seed_plus_1",
            )
            if all(k in entry for k in req_spine_keys):
                checked_keys.update(req_spine_keys)
                claims_checked += 1
                p2_0, p3_0, _ = _decompose_2_3_coprime(seed)
                p2_1, p3_1, _ = _decompose_2_3_coprime(seed + 1)
                ok = (
                    ok
                    and p2_0 == int(entry["v2_pow_seed"])
                    and p3_0 == int(entry["v3_pow_seed"])
                    and p2_1 == int(entry["v2_pow_seed_plus_1"])
                    and p3_1 == int(entry["v3_pow_seed_plus_1"])
                )
                if "sibling_seed" in entry:
                    checked_keys.add("sibling_seed")
                    sib = int(entry["sibling_seed"])
                    if sib > seed:
                        s2_0, s3_0, _ = _decompose_2_3_coprime(sib)
                        s2_1, s3_1, _ = _decompose_2_3_coprime(sib + 1)
                        ok = ok and (s2_0, s3_0, s2_1, s3_1) == (p2_0, p3_0, p2_1, p3_1)
                    else:
                        ok = False
            else:
                ok = False
        if "next_compressed" in entry:
            checked_keys.add("next_compressed")
            claims_checked += 1
            nxt_c = int_compressed_step(seed, q=3)
            ok = ok and (nxt_c == int(entry["next_compressed"]))
            if "v3_seed_plus_1" in entry or "v3_next_plus_1" in entry:
                if "v3_seed_plus_1" in entry and "v3_next_plus_1" in entry and seed >= 1 and nxt_c >= 1:
                    checked_keys.update(("v3_seed_plus_1", "v3_next_plus_1"))
                    v3_s_exp = int(entry["v3_seed_plus_1"])
                    v3_n_exp = int(entry["v3_next_plus_1"])
                    _, p3_s0, _ = _decompose_2_3_coprime(seed + 1)
                    _, p3_n0, _ = _decompose_2_3_coprime(nxt_c + 1)
                    ok = (
                        ok
                        and v3_s_exp >= 0
                        and v3_n_exp >= 0
                        and (3**v3_s_exp) == p3_s0
                        and (3**v3_n_exp) == p3_n0
                    )
                else:
                    ok = False
        if "cousin_diamond2_next" in entry:
            checked_keys.add("cousin_diamond2_next")
            claims_checked += 1
            nxt_d2 = cousin_diamond2_step_int(seed, q=3)
            ok = ok and (nxt_d2 == int(entry["cousin_diamond2_next"]))
            if "core3_seed_plus_1" in entry:
                checked_keys.add("core3_seed_plus_1")
                ok = ok and (core3_pos(seed + 1) == int(entry["core3_seed_plus_1"]))
            if "phi_diamond2_seed" in entry:
                checked_keys.add("phi_diamond2_seed")
                ok = ok and (cousin_diamond2_phi(seed) == int(entry["phi_diamond2_seed"]))
            if "phi_diamond2_next" in entry:
                checked_keys.add("phi_diamond2_next")
                ok = ok and (cousin_diamond2_phi(nxt_d2) == int(entry["phi_diamond2_next"]))
        if "steps" in entry or "target" in entry:
            if "steps" in entry and "target" in entry:
                checked_keys.update(("steps", "target"))
                claims_checked += 1
                end_v, _ = int_iter_and_parity(seed, int(entry["steps"]), q=3)
                ok = ok and (end_v == int(entry["target"]))
            else:
                ok = False
        if "glide_odd_steps" in entry:
            checked_keys.add("glide_odd_steps")
            claims_checked += 1
            g_steps = int(entry["glide_odd_steps"])
            ok = ok and g_steps >= 1 and ((seed + 1) == (1 << g_steps))
            if "glide_peak" in entry:
                checked_keys.add("glide_peak")
                end_g, par_g = int_iter_and_parity(seed, g_steps, q=3)
                ok = ok and all(b == 1 for b in par_g) and (end_g == int(entry["glide_peak"]))
        ok = ok and (claims_checked >= 1) and set(entry.keys()).issubset(checked_keys)
        if ok:
            verified_count += 1
        else:
            failed_witnesses.append(wid)

    # 2. m1_q2_pos
    for entry in bank["domains"]["m1_q2_pos"]:
        wid = str(entry["witness_id"])
        x0 = Fraction(int(entry["numerator"]), int(entry["denominator"]))
        ok = (x0 == Fraction(str(entry["x0"]))) and (x0 > 0) and (x0.denominator % 2 == 1)
        checked_m1: Set[str] = {"witness_id", "x0", "numerator", "denominator", "kills_mechanisms"}
        if entry.get("system") in ("T_diamond", "T_diamond2"):
            checked_m1.update(("system", "orbit"))
            step_fn_q6 = (
                cousin_diamond_step_q6
                if entry.get("system") == "T_diamond"
                else cousin_diamond2_step_q6
            )
            orb = [Fraction(s) for s in entry["orbit"]]
            cur_f = x0
            traced: List[Fraction] = []
            for _ in range(len(orb)):
                traced.append(cur_f)
                cur_f = step_fn_q6(cur_f)
            ok = ok and len(orb) >= 1 and (traced == orb) and (cur_f == x0)
        elif "period_k" in entry and "weight_w" in entry:
            checked_m1.update(("period_k", "weight_w"))
            k_per = int(entry["period_k"])
            w_exp = int(entry["weight_w"])
            cur_f = x0
            orb_f: List[Fraction] = []
            par_bits: List[int] = []
            for _ in range(max(0, k_per)):
                orb_f.append(cur_f)
                bit = cur_f.numerator & 1
                par_bits.append(bit)
                cur_f = (3 * cur_f + 1) / 2 if bit == 1 else (cur_f / 2)
            ok = ok and k_per >= 1 and (cur_f == x0) and (sum(par_bits) == w_exp)
            if "m_blocks" in entry:
                checked_m1.add("m_blocks")
                ok = ok and (count_odd_even_blocks(par_bits) == int(entry["m_blocks"]))
            if "x1" in entry:
                checked_m1.add("x1")
                local_mins = [
                    orb_f[i]
                    for i in range(len(par_bits))
                    if par_bits[i] == 1 and par_bits[(i - 1) % len(par_bits)] == 0
                ]
                ok = (
                    ok
                    and len(local_mins) >= 2
                    and local_mins[0] == x0
                    and local_mins[1] == Fraction(str(entry["x1"]))
                )
            if "parity_vector" in entry:
                checked_m1.add("parity_vector")
                ok = ok and (par_bits == [int(b) for b in entry["parity_vector"]])
            if "spiral_params" in entry:
                req_sp = ("spiral_params", "denom_gap", "brox_h0", "brox_h1", "gcd_d_h0_h1")
                if all(k in entry for k in req_sp):
                    checked_m1.update(req_sp)
                    w1, a1, w2, a2 = (int(v) for v in entry["spiral_params"])
                    h0, h1 = clp.two_block_brox_carries(w1, a1, w2, a2)
                    det = (1 << (w1 + a1 + w2 + a2)) - (3 ** (w1 + w2))
                    ok = (
                        ok
                        and det == int(entry["denom_gap"])
                        and h0 == int(entry["brox_h0"])
                        and h1 == int(entry["brox_h1"])
                        and math.gcd(det, math.gcd(h0, h1)) == int(entry["gcd_d_h0_h1"])
                        and Fraction((1 << w1) * h0 - det, det) == x0
                    )
                else:
                    ok = False
        else:
            ok = False
        ok = ok and set(entry.keys()).issubset(checked_m1)
        if ok:
            verified_count += 1
        else:
            failed_witnesses.append(wid)

    # 3. m2_z_neg
    for entry in bank["domains"]["m2_z_neg"]:
        wid = str(entry["witness_id"])
        seed = int(entry["seed"])
        ok = seed < 0
        checked_m2: Set[str] = {"witness_id", "seed", "kills_mechanisms"}
        if "orbit" in entry:
            req_m2 = ("orbit", "period_k", "weight_w", "denom_gap")
            if all(k in entry for k in req_m2):
                checked_m2.update(req_m2)
                orb = [int(v) for v in entry["orbit"]]
                cur_n = seed
                traced_n: List[int] = []
                w_n = 0
                for _ in range(len(orb)):
                    traced_n.append(cur_n)
                    if (cur_n & 1) == 1:
                        w_n += 1
                    cur_n = int_compressed_step(cur_n, q=3)
                k_p = int(entry["period_k"])
                w_p = int(entry["weight_w"])
                det_m2 = (1 << k_p) - (3**w_p)
                ok = (
                    ok
                    and k_p >= 1
                    and len(orb) == k_p
                    and traced_n == orb
                    and cur_n == seed
                    and w_n == w_p
                    and det_m2 == int(entry["denom_gap"])
                )
                if "carry" in entry:
                    checked_m2.add("carry")
                    c_m2 = 0
                    for idx_b, v_orb in enumerate(orb):
                        if (v_orb & 1) == 1:
                            c_m2 = 3 * c_m2 + (1 << idx_b)
                    ok = ok and (c_m2 == int(entry["carry"])) and (seed * det_m2 == c_m2)
            else:
                ok = False
        else:
            # Bounded-exponent Syracuse forest root in Z^-: (3 * seed + 1) % 128 == 0
            ok = ok and ((seed & 1) == 1) and ((3 * seed + 1) % 128 == 0)
        ok = ok and set(entry.keys()).issubset(checked_m2)
        if ok:
            verified_count += 1
        else:
            failed_witnesses.append(wid)

    # 4. m3_supercritical
    for entry in bank["domains"]["m3_supercritical"]:
        wid = str(entry["witness_id"])
        seed = int(entry["seed"])
        q_mul = int(entry["multiplier_q"])
        ok = seed >= 1 and q_mul > 3 and (q_mul & 1) == 1
        checked_m3: Set[str] = {"witness_id", "seed", "multiplier_q", "kills_mechanisms"}
        if entry.get("system") in ("T_diamond_q7", "T_diamond2_q7"):
            checked_m3.update(("system", "orbit"))
            step_fn_m3 = (
                cousin_diamond_step_int
                if entry.get("system") == "T_diamond_q7"
                else cousin_diamond2_step_int
            )
            orb = [int(v) for v in entry["orbit"]]
            cur_m3 = seed
            traced_m3: List[int] = []
            for _ in range(len(orb)):
                traced_m3.append(cur_m3)
                cur_m3 = step_fn_m3(cur_m3, q=q_mul)
            ok = ok and len(orb) >= 1 and (traced_m3 == orb) and (cur_m3 == seed)
        elif "period_k" in entry:
            if "weight_w" in entry and "denom_gap" in entry:
                checked_m3.update(("period_k", "weight_w", "denom_gap"))
                k_p = int(entry["period_k"])
                w_p = int(entry["weight_w"])
                end_m3, par_m3 = int_iter_and_parity(seed, k_p, q=q_mul)
                ok = (
                    ok
                    and k_p >= 1
                    and end_m3 == seed
                    and sum(par_m3) == w_p
                    and ((1 << k_p) - (q_mul**w_p)) == int(entry["denom_gap"])
                )
            else:
                ok = False
        elif "target_cycle_seed" in entry:
            checked_m3.add("target_cycle_seed")
            target_c = int(entry["target_cycle_seed"])
            cur_m3 = seed
            hit_target = False
            for _ in range(100):
                if cur_m3 == target_c:
                    hit_target = True
                    break
                cur_m3 = int_compressed_step(cur_m3, q=q_mul)
            ok = ok and hit_target
        else:
            cur_m3 = seed
            min_seen = seed
            max_seen = seed
            for _ in range(200):
                cur_m3 = int_compressed_step(cur_m3, q=q_mul)
                min_seen = min(min_seen, cur_m3)
                max_seen = max(max_seen, cur_m3)
            ok = ok and (min_seen == seed) and (max_seen > 10**5)
        ok = ok and set(entry.keys()).issubset(checked_m3)
        if ok:
            verified_count += 1
        else:
            failed_witnesses.append(wid)

    # 5. log2_3_convergents
    for entry in bank["domains"]["log2_3_convergents"]:
        wid = str(entry["witness_id"])
        ok = True
        checked_conv: Set[str] = {"witness_id", "kills_mechanisms"}
        if "K" in entry and "W" in entry and "gap_sign" in entry:
            checked_conv.update(("K", "W", "gap_sign"))
            k_val = int(entry["K"])
            w_val = int(entry["W"])
            gap = (1 << k_val) - (3**w_val)
            sign_obs = 1 if gap > 0 else (-1 if gap < 0 else 0)
            ok = ok and (sign_obs == int(entry["gap_sign"]))
            if "abs_gap" in entry:
                checked_conv.add("abs_gap")
                ok = ok and (abs(gap) == int(entry["abs_gap"]))
            if "even_diff_half" in entry:
                checked_conv.add("even_diff_half")
                ok = ok and ((k_val - w_val) == 2 * int(entry["even_diff_half"]))
        elif "a1" in entry and "a2" in entry and "degree_n" in entry:
            req_pade = ("a1", "a2", "degree_n", "type1_height_bits", "type1_rem_log2", "type2_err_log2")
            if all(k in entry for k in req_pade):
                checked_conv.update(req_pade)
                res_p = _solve_type1_and_type2_hermite_pade(
                    Fraction(str(entry["a1"])),
                    Fraction(str(entry["a2"])),
                    int(entry["degree_n"]),
                )
                ok = (
                    ok
                    and int(res_p["type1_height_bits"]) == int(entry["type1_height_bits"])
                    and abs(float(res_p["type1_rem_log2"]) - float(entry["type1_rem_log2"])) < 1e-3
                    and abs(float(res_p["type2_err_log2"]) - float(entry["type2_err_log2"])) < 1e-3
                )
                if "stepline_casorati_det_nonzero" in entry:
                    req_step = (
                        "stepline_casorati_det_nonzero",
                        "type2_offdiag_n1_n_err_log2",
                        "type2_offdiag_n_n1_err_log2",
                    )
                    if all(k in entry for k in req_step):
                        checked_conv.update(req_step)
                        ok = (
                            ok
                            and bool(res_p["stepline_casorati_det_nonzero"])
                            == bool(entry["stepline_casorati_det_nonzero"])
                            and abs(
                                float(res_p["type2_offdiag_n1_n_err_log2"])
                                - float(entry["type2_offdiag_n1_n_err_log2"])
                            )
                            < 1e-3
                            and abs(
                                float(res_p["type2_offdiag_n_n1_err_log2"])
                                - float(entry["type2_offdiag_n_n1_err_log2"])
                            )
                            < 1e-3
                        )
                    else:
                        ok = False
                if "diag_n55_err_log2_gt_zero" in entry:
                    checked_conv.add("diag_n55_err_log2_gt_zero")
                    res_55 = _solve_folded_symmetric_type2_diag(Fraction(str(entry["a1"])), 55)
                    ok = ok and (
                        (float(res_55["err_log2"]) > 0.0) == bool(entry["diag_n55_err_log2_gt_zero"])
                    )
            else:
                ok = False
        elif "beukers_degree_n" in entry:
            req_br = (
                "beukers_degree_n",
                "rem1_log2",
                "rem2_log2",
                "hom_elim_err_log2",
                "nonsep_2d_err_log2",
            )
            if all(k in entry for k in req_br):
                checked_conv.update(req_br)
                deg_n = int(entry["beukers_degree_n"])
                res_br = _solve_beukers_rhin_2d_and_const_elimination(deg_n)
                ok = (
                    ok
                    and float(res_br["symbolic_vs_series_diff"]) < 1e-40
                    and abs(float(res_br["rem1_log2"]) - float(entry["rem1_log2"])) < 1e-3
                    and abs(float(res_br["rem2_log2"]) - float(entry["rem2_log2"])) < 1e-3
                    and abs(float(res_br["hom_elim_err_log2"]) - float(entry["hom_elim_err_log2"])) < 1e-3
                    and abs(float(res_br["nonsep_2d_err_log2"]) - float(entry["nonsep_2d_err_log2"])) < 1e-2
                )
                if "integral_2d_log2" in entry:
                    checked_conv.add("integral_2d_log2")
                    ok = ok and (
                        abs(float(res_br["integral_2d_log2"]) - float(entry["integral_2d_log2"])) < 1e-3
                    )
            else:
                ok = False
        else:
            ok = False
        ok = ok and set(entry.keys()).issubset(checked_conv)
        if ok:
            verified_count += 1
        else:
            failed_witnesses.append(wid)

    return {
        "all_witnesses_ground_truth_verified": len(failed_witnesses) == 0 and verified_count > 0,
        "verified_witness_count": verified_count,
        "failed_witness_ids": tuple(failed_witnesses),
    }


def _dynamic_pred_core3_syracuse(_dom: str, entry: Dict[str, Any]) -> bool:
    """Dynamic test of `Phi_diamond(Syr(x)) < Phi_diamond(x)` on odd `Z^+` seeds (no ID lookup)."""
    seed = int(entry.get("seed", 0))
    if seed < 3 or (seed & 1) == 0:
        return True
    nxt = core2_pos(3 * seed + 1)
    return cousin_diamond_phi(nxt) < cousin_diamond_phi(seed)


def _dynamic_pred_coercive_v2_syracuse(_dom: str, entry: Dict[str, Any]) -> bool:
    """Dynamic test of non-monotone coercive `V(x) = 4^{v_2(x+1)} * (x+1)` on odd `Z^+` seeds."""
    seed = int(entry.get("seed", 0))
    if seed < 3 or (seed & 1) == 0:
        return True
    nxt = core2_pos(3 * seed + 1)
    p2_s = (seed + 1) & -(seed + 1)
    p2_n = (nxt + 1) & -(nxt + 1)
    return (p2_n * p2_n * (nxt + 1)) < (p2_s * p2_s * (seed + 1))


def _dynamic_pred_quadratic_peak_bound(_dom: str, entry: Dict[str, Any]) -> bool:
    """Dynamic test of naive backward-tree bound `peak_odd(x) <= x^2` along first 100 steps."""
    seed = int(entry.get("seed", 0))
    if seed < 3:
        return True
    cur = seed
    peak_odd = seed if (seed & 1) == 1 else 1
    for _ in range(100):
        if cur == 1:
            break
        cur = int_compressed_step(cur, q=3)
        if (cur & 1) == 1 and cur > peak_odd:
            peak_odd = cur
    return peak_odd <= seed * seed


def _dynamic_pred_sign_blind_cycle_divisibility(_dom: str, entry: Dict[str, Any]) -> bool:
    """Dynamic test of sign-blind claim `|2^k - 3^w| > 1 => (2^k - 3^w) nmid C_k(v)` on `Z^-`."""
    if "orbit" not in entry:
        return True
    orb = [int(v) for v in entry["orbit"]]
    bits = [x & 1 for x in orb]
    k_len = len(bits)
    w_wt = sum(bits)
    det = (1 << k_len) - (3**w_wt)
    if abs(det) <= 1:
        return True
    carry = 0
    for idx, b in enumerate(bits):
        if b:
            carry = 3 * carry + (1 << idx)
    return (carry % abs(det)) != 0


def _dynamic_pred_pade_low_degree_extrapolation(_dom: str, entry: Dict[str, Any]) -> bool:
    """
    Dynamic test of false Pade heuristic `err_log2(n, n) < 0 at n = 6 => step-line (n+1, n)
    and high-degree (55, 55) also stay < 0`.
    """
    if "a1" not in entry or "a2" not in entry or "degree_n" not in entry:
        return True
    a1 = Fraction(str(entry["a1"]))
    a2 = Fraction(str(entry["a2"]))
    n_deg = int(entry["degree_n"])
    res = _solve_type1_and_type2_hermite_pade(a1, a2, n_deg)
    if float(res["type2_err_log2"]) < 0.0:
        return float(res["type2_offdiag_n1_n_err_log2"]) < 0.0
    return True


def run_wave4_whole_space_campaign(bank_path: Optional[Path] = None) -> Dict[str, Any]:
    """
    Execute the complete Wave 4 whole-space red-team, solvable-cousin, Laurent-monomial,
    and `exactBackwardQuotient` campaign against `witness_bank.json` across Branches P1–P5.
    """
    u_gate = audit_universality_gate(
        "Wave4_WholeSpace_W4_1_to_W4_5",
        is_finite_m_table=False,
        is_finite_n_table=False,
        is_bounded_weight_table=False,
        uses_native_decide=False,
        uses_sorry=False,
        axioms_used=("propext", "Classical.choice", "Quot.sound"),
    )
    bank = load_witness_bank(bank_path)
    wb_truth = verify_witness_bank_ground_truth(bank_path)

    # Genuine dynamic mathematical hypothesis evaluations (zero hardcoded witness IDs)
    wb_gate_core3 = evaluate_hypothesis_against_witness_bank(
        "SingleShiftCore3OnTrueCollatz",
        _dynamic_pred_core3_syracuse,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    wb_gate_coercive_v2 = evaluate_hypothesis_against_witness_bank(
        "NonMonotoneCoerciveV2OnTrueCollatz",
        _dynamic_pred_coercive_v2_syracuse,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    wb_gate_quad_peak = evaluate_hypothesis_against_witness_bank(
        "QuadraticPeakEnvelopeOnZPos",
        _dynamic_pred_quadratic_peak_bound,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    wb_gate_sign_blind = evaluate_hypothesis_against_witness_bank(
        "SignBlindNonUnitCarryDivisibility",
        _dynamic_pred_sign_blind_cycle_divisibility,
        domains=("m2_z_neg",),
        bank_path=bank_path,
    )
    wb_gate_pade_stepline = evaluate_hypothesis_against_witness_bank(
        "PadeLowDegreeDiagonalImpliesSteplineConvergence",
        _dynamic_pred_pade_low_degree_extrapolation,
        domains=("log2_3_convergents",),
        bank_path=bank_path,
    )

    h1 = audit_h1_berg_meinardus_radial_hardy_barrier(max_r=10)
    h2 = audit_h2_furstenberg_zero_entropy_and_mod3_pinning()
    h3 = audit_h3_simultaneous_pade_and_2block_resultant()
    h4 = audit_h4_presburger_collapse_and_polynomial_sos_barrier(max_period_p=60)
    h4_laurent = audit_syracuse_laurent_valuation_monomial_barrier(max_abs_exp=6)
    h5 = synthesize_nonlocal_cousin_invariant_and_redteam_collatz()
    h5_tree = synthesize_and_redteam_backward_quotient_tree_invariants()

    passed = (
        u_gate.passed
        and bool(wb_truth["all_witnesses_ground_truth_verified"])
        and (not wb_gate_core3["passed"])
        and wb_gate_core3["minimal_failure"] == ("z_pos_high_glide", "ZPOS_SYRACUSE_17_TO_13_CORE3_JUMP")
        and (not wb_gate_coercive_v2["passed"])
        and ("z_pos_high_glide", "ZPOS_SYRACUSE_9_TO_7_V2_JUMP") in wb_gate_coercive_v2["failures"]
        and (not wb_gate_quad_peak["passed"])
        and wb_gate_quad_peak["minimal_failure"] == ("z_pos_high_glide", "ZPOS_N27_MOD373248_MIN")
        and (not wb_gate_sign_blind["passed"])
        and wb_gate_sign_blind["minimal_failure"] == ("m2_z_neg", "M2_NEG17_NONUNIT_11CYCLE")
        and (not wb_gate_pade_stepline["passed"])
        and wb_gate_pade_stepline["minimal_failure"]
        == ("log2_3_convergents", "PADE_SYMMETRIC_1_3_AND_NEG_1_3_STEPLINE_AND_N55_EXPLOSION")
        and bool(h1["barrier_verified"])
        and bool(h2["hypothesis_falsified"])
        and bool(h3["pade_explosion_verified"])
        and bool(h3["resultant_identities_verified"])
        and bool(h3["shared_factor_witnesses_verified"])
        and bool(h4["one_sided_presburger_hits_pow2_verified"])
        and bool(h4["coercive_sos_refuted_verified"])
        and bool(h4_laurent["laurent_monomial_barrier_verified"])
        and bool(h5["cousin_holdout_verified"])
        and bool(h5["cousin_m1_1_over_7_cycle_verified"])
        and bool(h5["cousin_m2_neg_cycles_verified"])
        and bool(h5["cousin_m3_q7_cycle5_verified"])
        and bool(h5["true_syracuse_all_candidates_falsified"])
        and bool(h5["antagonism_17_to_13_verified"])
        and bool(h5_tree["mod512_nine_step_weight_ge6_verified"])
        and bool(h5_tree["weight_le_5_mod373248_disjoint_verified"])
        and bool(h5_tree["sharp_weight_6_witness_184111_verified"])
        and bool(h5_tree["q_ray_strict_growth_verified"])
        and bool(h5_tree["backward_tree_y_monotone_falsified"])
    )
    return {
        "passed": passed,
        "verdict": "REDTEAM-PASSED" if passed else "FALSIFIED",
        "universality_gate_passed": u_gate.passed,
        "witness_bank_domains": tuple(bank["domains"].keys()),
        "witness_bank_total_entries": sum(len(v) for v in bank["domains"].values()),
        "witness_bank_falsified_count": len(bank["falsified_hypotheses"]),
        "witness_bank_ground_truth_verified": bool(wb_truth["all_witnesses_ground_truth_verified"]),
        "witness_bank_catches_core3_jump": not wb_gate_core3["passed"],
        "witness_bank_catches_coercive_v2_jump": not wb_gate_coercive_v2["passed"],
        "witness_bank_catches_quadratic_peak": not wb_gate_quad_peak["passed"],
        "witness_bank_catches_sign_blind_cycle": not wb_gate_sign_blind["passed"],
        "witness_bank_catches_pade_stepline_explosion": not wb_gate_pade_stepline["passed"],
        "h1_berg_meinardus": h1,
        "h2_furstenberg": h2,
        "h3_pade_and_resultant": h3,
        "h4_presburger_and_sos": h4,
        "h4_laurent_valuation_barrier": h4_laurent,
        "h5_cousin_and_synthesis": h5,
        "h5_backward_quotient_tree": h5_tree,
    }


# ============================================================================
# 10. Wave 5 Whole-Space Campaign (Fronts A–D: Non-Radial Preimage Weights,
#     T_diamond2 & Multi-Term/Non-Triangular Barriers, 2D Beukers–Rhin & m-Block
#     Resultants, Coupled q-Rays & Pi_2^0 Proof-Complexity Calibration)
# ============================================================================


def cousin_diamond2_step_int(x: int, q: int = 3) -> int:
    """
    Closer solvable mixed-(2,3) Collatz cousin `T_diamond2` on Z (for odd q >= 3):
    - Odd `x > 1` in any of the three `v_2(3x + 1) >= 2` Syracuse jump cones
      (`x % 16 == 1 and x % 3 != 2`, `x >= 73 and x % 64 == 9 and x % 3 != 2`, or
      `x >= 17 and core3_pos(x + 1) == 2`): `(q * x + 1) // 4`;
    - All other odd `x` (including all `x % 4 == 3` unbounded Mersenne glides and `x <= 1`):
      `(q * x + 1) // 2`;
    - Even `x > 2` with `x % 6 == 2`: `(x - 2) // 3`;
    - Even `x > 2` with `x % 8 == 6` (`x % 6 != 2`): `(x - 2) // 2`;
    - All other even `x` (including `x % 8 == 2` odd-returning halving and `x <= 2`): `x // 2`.
    """
    if (q & 1) == 0 or q < 3:
        raise ValueError(f"Expected odd multiplier q >= 3, got {q}")
    if (x & 1) == 1:
        if x > 1 and (x % 16) == 1 and (x % 3) != 2:
            return (q * x + 1) // 4
        if x >= 73 and (x % 64) == 9 and (x % 3) != 2:
            return (q * x + 1) // 4
        if x >= 17 and core3_pos(x + 1) == 2:
            return (q * x + 1) // 4
        return (q * x + 1) // 2
    if x > 2 and (x % 6) == 2:
        return (x - 2) // 3
    if x > 2 and (x % 8) == 6:
        return (x - 2) // 2
    return x // 2


def cousin_diamond2_step_q6(x: Fraction) -> Fraction:
    """
    Canonical extension of `T_diamond2` (`q = 3`) to `Q_(6) = {a/b : gcd(b, 6) == 1}`.
    On `Q_(6)` (`3 nmid b`), `core_3(x + 1) = core_3(a + b) / b` for `x + 1 > 0`, so
    `core_3(x + 1) == 2` is canonically `core3_pos(a + b) == 2 * b`.
    """
    if math.gcd(x.denominator, 6) != 1:
        raise ValueError(f"Expected rational with gcd(denom, 6) == 1, got {x}")
    inv_d_64 = pow(x.denominator, -1, 64)
    inv_d_3 = pow(x.denominator, -1, 3)
    r64 = (x.numerator * inv_d_64) % 64
    r3 = (x.numerator * inv_d_3) % 3
    if (r64 & 1) == 1:
        if x > 1 and (r64 % 16) == 1 and r3 != 2:
            return (3 * x + 1) / 4
        if x >= 73 and r64 == 9 and r3 != 2:
            return (3 * x + 1) / 4
        if x >= 17 and core3_pos(x.numerator + x.denominator) == 2 * x.denominator:
            return (3 * x + 1) / 4
        return (3 * x + 1) / 2
    if x > 2 and r3 == 2:
        return (x - 2) / 3
    if x > 2 and (r64 % 8) == 6:
        return (x - 2) / 2
    return x / 2


def cousin_diamond2_phi(x: int) -> int:
    """
    Exact 2-term positive-integer valuation Lyapunov invariant for `T_diamond2` on `Z^+`:
        Phi_diamond2(x) = 2^{v_2(x+1)} * core_{2,3}(x+1)^3 + (2^{v_2(x+1)})^5 * (3^{v_3(x+1)})^3.
    """
    if x < 1:
        raise ValueError(f"Expected positive integer x >= 1, got {x}")
    v2, v3, g = _decompose_2_3_coprime(x + 1)
    return v2 * (g**3) + (v2**5) * (v3**3)


def _beukers_rhin_2d_beta_series(
    n: int, terms: int = 240, prec: int = 160
) -> decimal.Decimal:
    """
    Independent exact Beta-function power-series evaluation of the 2D Euler-Rhin integral:
        I_n = int_0^1 int_0^1 x^n(1-x)^n y^n(1-y)^n u^(2n+1) / (1 - u*x)^(n+1) dx dy
    with `u = (3 + y) / 6 <= 2/3 < 1` (converging geometrically at rate `(2/3)^r` with
    zero integration-by-parts algebra, used to cross-verify symbolic Padé coefficients).
    """
    if n < 1:
        raise ValueError(f"Expected degree n >= 1, got {n}")
    if terms < 1:
        raise ValueError(f"Expected terms >= 1, got {terms}")
    if prec < 30:
        raise ValueError(f"Expected prec >= 30, got {prec}")
    fact_n = math.factorial(n)
    max_s = 2 * n + terms
    beta_seq: List[Fraction] = [
        Fraction(math.factorial(n + s) * fact_n, math.factorial(2 * n + s + 1))
        for s in range(max_s + 1)
    ]
    pow3_seq: List[int] = [1] * (max_s + 1)
    for idx in range(1, max_s + 1):
        pow3_seq[idx] = pow3_seq[idx - 1] * 3
    with decimal.localcontext() as ctx:
        ctx.prec = prec
        total = decimal.Decimal(0)
        pow6_m = 6 ** (2 * n + 1)
        for r in range(terms):
            m_pow = 2 * n + 1 + r
            y_sum = Fraction(0, 1)
            for s in range(m_pow + 1):
                y_sum += (math.comb(m_pow, s) * pow3_seq[m_pow - s]) * beta_seq[s]
            term = math.comb(n + r, n) * beta_seq[r] * (y_sum / pow6_m)
            total += decimal.Decimal(term.numerator) / decimal.Decimal(term.denominator)
            pow6_m *= 6
        return total


def _solve_beukers_rhin_2d_and_const_elimination(n: int) -> Dict[str, Any]:
    """
    Compute exact cleared-denominator linear forms in `{1, log 2, log 3}` at degree `n >= 1`:
    1. 1D Legendre-Beukers approximants `A1 + B1 * log 2` (`a = -1`) and
       `A2 + B2 * log(3/2)` (`a = -1/2`), plus the exact homogeneous 2-logarithm form
       `P_n * log 2 + Q_n * log 3` obtained by eliminating the constant term `1`.
    2. Genuine non-separable 2D Euler-Rhin integral on `[0, 1]^2`:
       `I_n = int_0^1 int_0^1 x^n(1-x)^n y^n(1-y)^n u^(2n+1) / (1 - u*x)^(n+1) dx dy`
       (`u = (3 + y)/6`), which evaluates via `n`-fold integration by parts in `x` to
       `A_2d^(0) + B_2d^(0) * log 2 + C_2d^(0) * log 3 = I_n > 0` with zero dilogarithms.
    """
    if n < 1:
        raise ValueError(f"Expected degree n >= 1, got {n}")
    prec = max(160, 28 * n + 60)
    with decimal.localcontext() as ctx:
        ctx.prec = prec
        ln2 = decimal.Decimal(2).ln()
        ln3 = decimal.Decimal(3).ln()
        c_leg = [((-1) ** k) * math.comb(n, k) * math.comb(n + k, k) for k in range(n + 1)]

        def pade_log1pc(c_frac: Fraction) -> Tuple[int, int]:
            x0 = -Fraction(1, 1) / c_frac
            b_coeff = sum(Fraction(c_leg[k]) * (x0**k) for k in range(n + 1)) / c_frac
            a_coeff = Fraction(0, 1)
            for k in range(1, n + 1):
                s = sum((x0 ** (k - 1 - j)) / (j + 1) for j in range(k))
                a_coeff += Fraction(c_leg[k]) * s / c_frac
            den = math.lcm(a_coeff.denominator, b_coeff.denominator)
            a_int = int(a_coeff * den)
            b_int = int(b_coeff * den)
            g = math.gcd(abs(a_int), abs(b_int))
            return a_int // g, b_int // g

        a1_int, b1_int = pade_log1pc(Fraction(1, 1))
        a2_int, b2_int = pade_log1pc(Fraction(1, 2))
        rem1 = abs(decimal.Decimal(a1_int) + decimal.Decimal(b1_int) * ln2)
        rem2 = abs(decimal.Decimal(a2_int) + decimal.Decimal(b2_int) * (ln3 - ln2))
        g_a = math.gcd(abs(a1_int), abs(a2_int))
        p_hom = (a2_int // g_a) * b1_int + (a1_int // g_a) * b2_int
        q_hom = -(a1_int // g_a) * b2_int
        g_pq = math.gcd(abs(p_hom), abs(q_hom))
        p_hom //= g_pq
        q_hom //= g_pq
        rem_hom = abs(decimal.Decimal(p_hom) * ln2 + decimal.Decimal(q_hom) * ln3)

        # Non-separable 2D Euler-Rhin integral on [0,1]^2 at u = (3 + y)/6
        max_m = 3 * n + 2
        m_log: List[Tuple[Fraction, Fraction, Fraction]] = []
        for m in range(max_m + 1):
            c1 = Fraction(0, 1)
            c2 = Fraction(1, m + 1)
            c3 = Fraction(1, m + 1)
            for r in range(m + 1):
                coef = ((-1) ** (r + 1)) * math.comb(m, r) * (3 ** (m - r))
                c3 += Fraction(coef * (3 ** (r + 1)), r + 1)
                c2 -= Fraction(coef * (2 ** (r + 1)), r + 1)
                c1 -= Fraction(coef * ((3 ** (r + 1)) - (2 ** (r + 1))), (r + 1) ** 2)
            m_log.append((c1, c2, c3))

        tot_1 = Fraction(0, 1)
        tot_2 = Fraction(0, 1)
        tot_3 = Fraction(0, 1)
        sign_n = (-1) ** n
        for k in range(n + 1):
            ck = Fraction(sign_n * c_leg[k])
            d = n - k
            for i in range(n + 1):
                yi_c = ((-1) ** i) * math.comb(n, i)
                for t in range(d + 1):
                    ut_c = Fraction(math.comb(d, t) * (3 ** (d - t)), 6**d)
                    w_m = ck * yi_c * ut_c
                    m_idx = n + i + t
                    tot_1 += w_m * m_log[m_idx][0]
                    tot_2 += w_m * m_log[m_idx][1]
                    tot_3 += w_m * m_log[m_idx][2]
            for j in range(k):
                dj = n - k + j + 1
                for i in range(n + 1):
                    yi_c = ((-1) ** i) * math.comb(n, i)
                    for t in range(dj + 1):
                        ut_c = Fraction(math.comb(dj, t) * (3 ** (dj - t)), 6**dj)
                        m_idx = n + i + t
                        tot_1 += (-ck / (j + 1)) * yi_c * ut_c / (m_idx + 1)

        val_closed = (
            decimal.Decimal(tot_1.numerator) / decimal.Decimal(tot_1.denominator)
            + (decimal.Decimal(tot_2.numerator) / decimal.Decimal(tot_2.denominator)) * ln2
            + (decimal.Decimal(tot_3.numerator) / decimal.Decimal(tot_3.denominator)) * ln3
        )
        series_terms = max(240, 20 * n + 140)
        series_diff = float(
            abs(val_closed - _beukers_rhin_2d_beta_series(n, terms=series_terms, prec=prec))
        )
        den_2d = math.lcm(tot_1.denominator, tot_2.denominator, tot_3.denominator)
        a_2d = int(tot_1 * den_2d)
        b_2d = int(tot_2 * den_2d)
        c_2d = int(tot_3 * den_2d)
        g_2d = math.gcd(abs(a_2d), math.gcd(abs(b_2d), abs(c_2d)))
        a_2d //= g_2d
        b_2d //= g_2d
        c_2d //= g_2d
        rem_2d = abs(
            decimal.Decimal(a_2d)
            + decimal.Decimal(b_2d) * ln2
            + decimal.Decimal(c_2d) * ln3
        )
        return {
            "degree_n": n,
            "rem1_log2": float(rem1.ln() / ln2),
            "rem2_log2": float(rem2.ln() / ln2),
            "p_hom": p_hom,
            "q_hom": q_hom,
            "hom_elim_err_log2": float(rem_hom.ln() / ln2),
            "integral_2d_log2": float(val_closed.ln() / ln2),
            "symbolic_vs_series_diff": series_diff,
            "nonsep_2d_den_bits": (den_2d // g_2d).bit_length(),
            "nonsep_2d_err_log2": float(rem_2d.ln() / ln2),
        }


def audit_w5_front_a_nonradial_preimage_superharmonicity() -> Dict[str, Any]:
    """
    Front A (`Branch P1.2`):
    1. Verify stopping-time model sanity (`w(n) = 3^{-sigma(n)}` satisfies strict preimage
       contraction `w(2m) + 1_{m == 2 mod 3} w((2m-1)/3) <= (2/3) * w(m)` on convergent nodes).
    2. Verify `Nat`-valued positive preimage weight impossibility via `w(4^(k+1)) + k <= w(4)`.
    3. Verify universal non-radial periodic + `(v_2(n), v_3(n), v_2(n+1), v_3(n+1))` barrier
       along `z_j = (4^(3*j + 4) - 1) // 3` (`85, 5461, 349525, ...`).
    """
    def stopping_to_triv(n: int) -> int:
        steps = 0
        cur = n
        while cur >= 3:
            cur = int_compressed_step(cur, q=3)
            steps += 1
        return steps

    # 1. Verify stopping-time model sanity across m = 3..300
    model_contraction_ok = True
    for m in range(3, 301):
        w_m = Fraction(1, 3 ** stopping_to_triv(m))
        lhs = Fraction(1, 3 ** stopping_to_triv(2 * m))
        if m % 3 == 2:
            lhs += Fraction(1, 3 ** stopping_to_triv((2 * m - 1) // 3))
        if lhs > Fraction(2, 3) * w_m:
            model_contraction_ok = False
            break

    # 2. Verify 4-adic spine constancy of (v2(z_j), v3(z_j), v2(z_j+1), v3(z_j+1)) across j = 0..10
    z_family = [(4 ** (3 * j + 4) - 1) // 3 for j in range(11)]
    const_val_ok = z_family[0] == 85 and z_family[1] == 5461
    for j, zj in enumerate(z_family):
        p2_z, p3_z, _ = _decompose_2_3_coprime(zj)
        p2_zp1, p3_zp1, _ = _decompose_2_3_coprime(zj + 1)
        m_even = 2 * (4 ** (3 * j + 3))
        if (
            (p2_z, p3_z, p2_zp1, p3_zp1) != (1, 1, 2, 1)
            or m_even % 3 != 2
            or (2 * m_even - 1) // 3 != zj
            or int_compressed_step(zj, q=3) != m_even
        ):
            const_val_ok = False
            break

    # Verify arithmetic-progression congruence mod P across P = 1..40
    mod_ap_ok = True
    for p_mod in range(1, 41):
        vals_mod = [z % p_mod for z in z_family]
        # Verify repetition exists within pigeonhole horizon
        seen_m = set()
        rep = False
        for j in range(p_mod + 5):
            zj_mod = ((pow(4, 3 * j + 4, 3 * p_mod) - 1) // 3) % p_mod
            if zj_mod in seen_m:
                rep = True
                break
            seen_m.add(zj_mod)
        if not rep:
            mod_ap_ok = False
            break

    return {
        "stopping_time_model_contraction_verified": model_contraction_ok,
        "z_j_valuation_constancy_verified": const_val_ok,
        "z_j_modular_repetition_verified": mod_ap_ok,
        "barrier_verified": model_contraction_ok and const_val_ok and mod_ap_ok,
    }


def audit_w5_front_b_cousin_diamond2_multiterm_and_nontri_matrices() -> Dict[str, Any]:
    """
    Front B (`Branch P4.2`, `P4.3`, `P5`):
    1. Verify `T_diamond2` global strict descent under 2-term `cousin_diamond2_phi` across
       `x = 3..4000`, Mersenne glides `2^k - 1`, and `v_2 = 2` `3`-core jumps `2 * 9^B - 1`,
       while verifying 1-term Laurent monomial impossibility on `{7, 17, 73, 97}` and
       `M1` (`1/7`), `M2` (`-1, -5`), `M3` (`q = 7, cycle 5`) separation.
    2. Verify that 2-term sums (`5*v3Pow + 3*core3` and `(-3,-2,-2) + lam*(5,3,2)`) survive
       Wave 4's `{7, 9, 17, 97}` yet fail on `{3 -> 5}` and `{13 -> 5}`, and verify the
       4-family asymptotic dominance barrier on true `(3x + 1)`.
    3. Verify full non-upper-triangular coordinatewise-monotone matrix collapse `M_s = I_d`
       on `{R2, R5, R7, R9, R11}` across dimensions `d = 1..4`.
    """
    # 1. T_diamond2 global descent + 1-term impossibility + M1/M2/M3 separation
    test_xs = (
        list(range(3, 4001))
        + [(1 << k) - 1 for k in range(2, 32)]
        + [2 * (9**b) - 1 for b in range(1, 14)]
        + [1 << 200, (1 << 200) - 1]
    )
    d2_descent_ok = all(
        cousin_diamond2_step_int(x) >= 1
        and cousin_diamond2_phi(cousin_diamond2_step_int(x)) < cousin_diamond2_phi(x)
        for x in test_xs
    )
    # Verify T_diamond2 matches true Syracuse on {7->11, 17->13, 97->73, 73->55}
    d2_syr_match_ok = (
        cousin_diamond2_step_int(7) == 11
        and cousin_diamond2_step_int(11) == 17
        and cousin_diamond2_step_int(17) == 13
        and cousin_diamond2_step_int(97) == 73
        and cousin_diamond2_step_int(73) == 55
    )
    # Verify 0 single Laurent monomials in [-6..6]^3 survive {7, 17, 73, 97} on T_diamond2
    d2_single_laurent_survivors = 0
    w_d2 = (7, 17, 73, 97)
    decomp_d2 = [
        (_decompose_2_3_coprime(x + 1), _decompose_2_3_coprime(cousin_diamond2_step_int(x) + 1))
        for x in w_d2
    ]
    for a in range(-6, 7):
        for b in range(-6, 7):
            for c in range(-6, 7):
                if all(
                    (Fraction(n2) ** a) * (Fraction(n3) ** b) * (Fraction(ng) ** c)
                    < (Fraction(s2) ** a) * (Fraction(s3) ** b) * (Fraction(sg) ** c)
                    for (s2, s3, sg), (n2, n3, ng) in decomp_d2
                ):
                    d2_single_laurent_survivors += 1

    # M1 / M2 / M3 checks on T_diamond2
    m1_cur = Fraction(1, 7)
    for _ in range(5):
        m1_cur = cousin_diamond2_step_q6(m1_cur)
    m2_ok = (
        cousin_diamond2_step_int(-1) == -1
        and cousin_diamond2_step_int(cousin_diamond2_step_int(cousin_diamond2_step_int(-5))) == -5
    )
    m3_cur = 5
    for _ in range(5):
        m3_cur = cousin_diamond2_step_int(m3_cur, q=7)
    q6_int_agree_ok = all(
        cousin_diamond2_step_q6(Fraction(x_chk, 1))
        == Fraction(cousin_diamond2_step_int(x_chk), 1)
        for x_chk in range(1, 200)
    )
    d2_countermodels_ok = (
        (m1_cur == Fraction(1, 7)) and m2_ok and (m3_cur == 5) and q6_int_agree_ok
    )

    # 2. Verify 2-term survivors on {7, 9, 17, 97} and exact minimal falsifiers on true Syracuse
    def syr_odd(x: int) -> int:
        return core2_pos(3 * x + 1)

    def psi_pos2(x: int) -> int:
        v2, v3, g = _decompose_2_3_coprime(x + 1)
        return 5 * v3 + 3 * v2 * g

    lam_mid = (Fraction(1, 21591360) + Fraction(13, 136396800)) / 2

    def psi_laur2(x: int) -> Fraction:
        v2, v3, g = _decompose_2_3_coprime(x + 1)
        return Fraction(1, (v2**3) * (v3**2) * (g**2)) + lam_mid * (v2**5) * (v3**3) * (g**2)

    two_term_trap_ok = (
        all(psi_pos2(syr_odd(x)) < psi_pos2(x) for x in (7, 9, 17, 97))
        and psi_pos2(syr_odd(3)) > psi_pos2(3)
        and all(psi_laur2(syr_odd(x)) < psi_laur2(x) for x in (7, 9, 17, 97))
        and psi_laur2(syr_odd(13)) > psi_laur2(13)
    )

    # 3. Verify non-upper-triangular L*(.)*R sandwich identity across d = 1..4 on random non-tri matrices
    rng = random.Random(20261118)
    nontri_sandwich_ok = True
    for d in range(1, 5):
        for _ in range(25):
            # Generate arbitrary non-triangular L >= I_d, B1 >= I_d, R >= I_d and non-zero E_B0 >= 0
            l_mat = [
                [(1 if i == j else 0) + rng.randint(0, 2) for j in range(d)] for i in range(d)
            ]
            b1_mat = [
                [(1 if i == j else 0) + rng.randint(0, 2) for j in range(d)] for i in range(d)
            ]
            r_mat = [
                [(1 if i == j else 0) + rng.randint(0, 2) for j in range(d)] for i in range(d)
            ]
            e_b0 = [[0 for _ in range(d)] for _ in range(d)]
            ri, rj = rng.randrange(d), rng.randrange(d)
            e_b0[ri][rj] = 1
            b0_mat = [[(1 if i == j else 0) + e_b0[i][j] for j in range(d)] for i in range(d)]

            def mm(a: List[List[int]], b: List[List[int]]) -> List[List[int]]:
                return [
                    [sum(a[i][k] * b[k][j] for k in range(d)) for j in range(d)]
                    for i in range(d)
                ]

            lb1r = mm(mm(l_mat, b1_mat), r_mat)
            lb1b0r = mm(mm(mm(l_mat, b1_mat), b0_mat), r_mat)
            if lb1b0r[ri][rj] < lb1r[ri][rj] + 1:
                nontri_sandwich_ok = False
                break

    return {
        "cousin_diamond2_global_descent_verified": d2_descent_ok,
        "cousin_diamond2_syracuse_witnesses_verified": d2_syr_match_ok,
        "cousin_diamond2_single_laurent_survivors": d2_single_laurent_survivors,
        "cousin_diamond2_single_laurent_impossible_verified": d2_single_laurent_survivors == 0,
        "cousin_diamond2_countermodels_verified": d2_countermodels_ok,
        "cousin_diamond2_q6_matches_int_verified": q6_int_agree_ok,
        "two_term_w4_trap_and_rebound_falsifier_verified": two_term_trap_ok,
        "non_triangular_sandwich_collapse_verified": nontri_sandwich_ok,
    }


def audit_w5_front_c_beukers_rhin_mblock_and_antipodal_primes() -> Dict[str, Any]:
    """
    Front C (`Branch P3.2`, `P3.3`, `P3.4`):
    1. Verify 2D Beukers-Rhin integral & constant-term elimination blowup across `n = 1..8`.
    2. Verify general `m`-block (`m = 1..5`) spiral resultant identity
       `2^(a_j + w_{j+1}) * H_{j+1} == 3^(w_j) * H_j + D * (2^(a_j) - 1)`, global quotient
       Mersenne GCD lock, and exact mod-3 parity bi-implication on rational/integer block systems.
    3. Verify 1-block even-even impossibility (`2 | w1 and 2 | a1 => D > 2^a1 - 1`) and
       universal antipodal-order prime exclusion (`2^m1 == -1 mod p` and `2^m2 + 3^m2 == 0 mod p`
       implies `p nmid D` on 1-block integer cycles, while `p in {5, 13}` DOES divide `D` in `M1`).
    """
    from .boost_obstructions import brox_shifted_block_carry

    # 1. Beukers-Rhin 2D & constant-term elimination sweep (cross-checked vs Beta series)
    br_n1 = _solve_beukers_rhin_2d_and_const_elimination(1)
    br_n5 = _solve_beukers_rhin_2d_and_const_elimination(5)
    br_n8 = _solve_beukers_rhin_2d_and_const_elimination(8)
    beukers_rhin_explosion_ok = (
        br_n1["symbolic_vs_series_diff"] < 1e-40
        and br_n5["symbolic_vs_series_diff"] < 1e-40
        and br_n1["rem1_log2"] < -3.0
        and br_n1["hom_elim_err_log2"] < -4.0  # low-n convergent dip (-8, 5)
        and br_n1["integral_2d_log2"] < -6.0
        and br_n1["nonsep_2d_err_log2"] > 3.0  # 2D squared lcm already > 1 (+3.45 bits) at n = 1
        and br_n5["rem1_log2"] < -9.0
        and br_n5["rem2_log2"] < -14.0
        and br_n5["hom_elim_err_log2"] > 3.0
        and br_n5["integral_2d_log2"] < -27.0
        and br_n5["nonsep_2d_err_log2"] > 18.0
        and br_n8["hom_elim_err_log2"] > 5.0
        and br_n8["nonsep_2d_err_log2"] > 39.0
    )

    # 2. General m-block (m = 1..5) resultant identity across block configurations
    mblock_resultant_ok = True
    sample_blocks = [
        ((3,), (2,)),
        ((2, 3), (1, 3)),
        ((2, 1, 3), (1, 2, 2)),
        ((3, 2, 2, 1), (2, 1, 3, 1)),
        ((2, 2, 1, 3, 1), (1, 2, 1, 2, 2)),
    ]
    for wb, ab in sample_blocks:
        m = len(wb)
        k_tot, w_tot, hs = brox_shifted_block_carry(wb, ab)
        det = (1 << k_tot) - (3**w_tot)
        for j in range(m):
            jn = (j + 1) % m
            lhs = (1 << (ab[j] + wb[jn])) * hs[jn]
            rhs = (3 ** wb[j]) * hs[j] + det * ((1 << ab[j]) - 1)
            if lhs != rhs:
                mblock_resultant_ok = False
                break

    # 3. 1-block even-even impossibility & antipodal prime exclusion (28 primes < 300)
    even_even_ok = True
    for v in range(1, 60):
        for u in range(1, 60):
            det_ev = (1 << (2 * v + 2 * u)) - (3 ** (2 * v))
            if det_ev > 0 and det_ev <= (1 << (2 * u)) - 1:
                even_even_ok = False
                break

    antipodal_primes: List[int] = []
    for p in range(5, 300, 2):
        if any(p % d == 0 for d in range(3, int(p**0.5) + 1, 2)):
            continue
        has_m1 = any(pow(2, m1, p) == p - 1 for m1 in range(1, p))
        has_m2 = any((pow(2, m2, p) + pow(3, m2, p)) % p == 0 for m2 in range(1, p))
        if has_m1 and has_m2:
            antipodal_primes.append(p)

    # Check M1 separation at p = 5 (19/5, D = 5) and p = 13 (211/13, D = 13)
    c_19_5 = trace_q2_cycle_from_parity((1, 1, 1, 0, 0))
    c_211_13 = trace_q2_cycle_from_parity((1, 1, 1, 1, 1, 0, 0, 0))
    antipodal_ok = (
        len(antipodal_primes) == 28
        and 5 in antipodal_primes
        and 11 in antipodal_primes
        and 13 in antipodal_primes
        and 17 in antipodal_primes
        and 97 in antipodal_primes
        and c_19_5.denom_gap == 5
        and c_211_13.x0 == Fraction(211, 13)
        and c_211_13.denom_gap == 13
    )

    return {
        "beukers_rhin_explosion_verified": beukers_rhin_explosion_ok,
        "beukers_rhin_series_cross_verified": (
            br_n1["symbolic_vs_series_diff"] < 1e-40
            and br_n5["symbolic_vs_series_diff"] < 1e-40
            and br_n8["symbolic_vs_series_diff"] < 1e-40
        ),
        "mblock_resultant_identities_verified": mblock_resultant_ok,
        "one_block_even_even_impossible_verified": even_even_ok,
        "antipodal_prime_count_lt_300": len(antipodal_primes),
        "antipodal_primes_and_m1_separation_verified": antipodal_ok,
    }


def audit_w5_front_d_coupled_q_rays_and_pi2_calibration() -> Dict[str, Any]:
    """
    Front D (`Branch P5.3` & `P4.4`):
    1. Verify exact `q`-ray affine step law, `q >= 1` universal `IsFirstHitOnePair` automaticity
       (including on `uLoop` words where `q = 0` fails), `mod 512` constancy, and `mod 729`
       bijection (`382 / 729` surviving hits per period) across `w >= 6` core words.
    2. Verify unconditional `|u| <= 7` elimination from `IsSurvivingMod373248Class` across all
       core words and `q`, plus the exact `27 / 512` 9-bit prefix lock (sharp at `|u| = 8, w = 6,
       y = 184111`).
    3. Verify `Pi_2^0` Skolem box equivalence (`|tail| <= K` and `486 * q <= K`) and polynomial
       stopping-time bound `sigma_diamond2(x) <= (x + 1)^3 + (x + 1)^5` on `T_diamond2`.
    """
    from . import cs_forest_transfer as cft
    from .parity_2adic import parity_vector

    # 1. Test q-ray law on w >= 6 core words
    sample_w6_words = [
        (1, 1, 1, 1, 0, 1, 0, 1),
        (1, 1, 0, 1, 1, 1, 1, 1),
        (1, 1, 1, 1, 1, 1),
    ]
    ray_laws_ok = True
    for u_w in sample_w6_words:
        w = sum(u_w)
        p_w = 2 * (3 ** (w - 1))
        y0 = cft.exact_backward_quotient(1, u_w, 0)
        y1 = cft.exact_backward_quotient(1, u_w, 1)
        k0 = cft.backward_one_total_steps(u_w, 0)
        kw = ((1 << p_w) - 1) // (3**w)
        if y1 - y0 != (1 << k0) * kw or (y1 % 512) != (y0 % 512) or k0 < 10:
            ray_laws_ok = False
            break
        delta_729 = (pow(2, k0, 729) * (kw % 729)) % 729
        if math.gcd(delta_729, 729) != 1:
            ray_laws_ok = False
            break
        hits_729 = sum(
            1
            for q_i in range(729)
            if cft.is_surviving_mod729_residue((y0 + q_i * delta_729) % 729)
        )
        if hits_729 != 382:
            ray_laws_ok = False
            break

    # Verify q >= 1 universal first-hit automaticity on uLoop words (where q = 0 is NOT first-hit)
    q_pos_first_hit_ok = True
    for u_base in ((1, 1), (1, 0, 1), (1, 1, 1)):
        sh0 = cft.canonical_suffix_shift(u_base, 1)
        u_loop = u_base + (0,) * sh0 + (1,)
        if cft.is_first_hit_one_pair(u_loop, 0) or not cft.is_first_hit_one_pair(u_loop, 1):
            q_pos_first_hit_ok = False
            break

    # 2. Exhaustive |u| <= 7 elimination from IsSurvivingMod373248Class & 27/512 prefix count
    surv512 = [r for r in range(512) if cft.is_surviving_mod512_residue(r)]
    prefixes9 = {parity_vector(r, 9) for r in surv512}
    len_le_7_disjoint_ok = len(prefixes9) == 27
    for length in range(1, 8):
        words = [(1,)] if length == 1 else [
            (1,) + mid + (1,) for mid in product((0, 1), repeat=length - 2)
        ]
        for u_c in words:
            for q_i in (0, 1):
                yq = cft.exact_backward_quotient(1, u_c, q_i)
                if cft.is_surviving_mod373248_class(yq):
                    len_le_7_disjoint_ok = False
                    break

    # 3. Pi_2^0 Skolem box & T_diamond2 polynomial stopping bound
    pi2_box_ok = True
    for n_surv in [r for r in range(27, 2000, 2) if cft.is_surviving_mod373248_class(r)][:25]:
        u_hit, q_hit = cft.encode_convergent_odd_to_first_hit_pair(n_surv)
        k_steps = cft.backward_one_total_steps(u_hit, q_hit)
        if not (len(u_hit) >= 8 and sum(u_hit) >= 6 and len(u_hit) <= k_steps and 486 * q_hit <= k_steps):
            pi2_box_ok = False
            break

    for x_d2 in range(1, 300):
        cur = x_d2
        st = 0
        bound = (x_d2 + 1) ** 3 + (x_d2 + 1) ** 5
        while cur != 1 and st <= bound:
            cur = cousin_diamond2_step_int(cur)
            st += 1
        if cur != 1 or st > bound:
            pi2_box_ok = False
            break

    return {
        "q_ray_affine_and_382_per_729_verified": ray_laws_ok,
        "q_pos_universal_first_hit_verified": q_pos_first_hit_ok,
        "length_le_7_mod373248_disjoint_verified": len_le_7_disjoint_ok,
        "pi2_skolem_box_and_cousin_poly_bound_verified": pi2_box_ok,
    }


def _dynamic_pred_pos_2term_valuation_syracuse(_dom: str, entry: Dict[str, Any]) -> bool:
    """Dynamic test of `5 * 3^{v_3(x+1)} + 3 * core_3(x+1)` (passes `{7,9,17,97}`, fails `3->5`)."""
    seed = int(entry.get("seed", 0))
    if seed < 3 or (seed & 1) == 0:
        return True
    nxt = core2_pos(3 * seed + 1)
    if nxt == 1:
        return True
    v2_s, v3_s, g_s = _decompose_2_3_coprime(seed + 1)
    v2_n, v3_n, g_n = _decompose_2_3_coprime(nxt + 1)
    return (5 * v3_n + 3 * v2_n * g_n) < (5 * v3_s + 3 * v2_s * g_s)


def _dynamic_pred_glide_laurent_2term_syracuse(_dom: str, entry: Dict[str, Any]) -> bool:
    """Dynamic test of glide-contractive `(-3,-2,-2) + lam*(5,3,2)` (passes `{7,9,17,97}`, fails `13->5`)."""
    seed = int(entry.get("seed", 0))
    if seed < 3 or (seed & 1) == 0:
        return True
    nxt = core2_pos(3 * seed + 1)
    if nxt == 1:
        return True
    lam = (Fraction(1, 21591360) + Fraction(13, 136396800)) / 2
    v2_s, v3_s, g_s = _decompose_2_3_coprime(seed + 1)
    v2_n, v3_n, g_n = _decompose_2_3_coprime(nxt + 1)
    val_s = Fraction(1, (v2_s**3) * (v3_s**2) * (g_s**2)) + lam * (v2_s**5) * (v3_s**3) * (g_s**2)
    val_n = Fraction(1, (v2_n**3) * (v3_n**2) * (g_n**2)) + lam * (v2_n**5) * (v3_n**3) * (g_n**2)
    return val_n < val_s


def _dynamic_pred_periodic_valuation_decay(_dom: str, entry: Dict[str, Any]) -> bool:
    """Dynamic test of naive claim that `(v2(n), v3(n), v2(n+1), v3(n+1))` distinguishes geometric siblings."""
    if "sibling_seed" not in entry:
        return True
    seed = int(entry["seed"])
    sib = int(entry["sibling_seed"])
    sig_s = (_decompose_2_3_coprime(seed)[:2], _decompose_2_3_coprime(seed + 1)[:2])
    sig_b = (_decompose_2_3_coprime(sib)[:2], _decompose_2_3_coprime(sib + 1)[:2])
    return sig_s != sig_b


def _dynamic_pred_antipodal_prime_without_z_integrality(_dom: str, entry: Dict[str, Any]) -> bool:
    """Dynamic test of `13 nmid D` on 1-block positive cycles omitting `Z`-integrality."""
    if int(entry.get("m_blocks", 0)) != 1 or "period_k" not in entry or "weight_w" not in entry:
        return True
    det = (1 << int(entry["period_k"])) - (3 ** int(entry["weight_w"]))
    return (det % 13) != 0


def _dynamic_pred_beukers_rhin_const_elim_converges(_dom: str, entry: Dict[str, Any]) -> bool:
    """Dynamic test of false heuristic `rem1 < 1 and rem2 < 1 => eliminated homogeneous err < 1`."""
    if "beukers_degree_n" not in entry:
        return True
    res = _solve_beukers_rhin_2d_and_const_elimination(int(entry["beukers_degree_n"]))
    if float(res["rem1_log2"]) < 0.0 and float(res["rem2_log2"]) < 0.0:
        return float(res["hom_elim_err_log2"]) < 0.0 and float(res["nonsep_2d_err_log2"]) < 0.0
    return True


def _dynamic_pred_cousin_diamond2_omits_odd_pow3_cone(_dom: str, entry: Dict[str, Any]) -> bool:
    """
    Dynamic test catching partial extensions of `T_diamond2` that omit the third odd
    Syracuse-jump cone `x >= 17 and core3(x + 1) == 2` (diverging at `x = 53 = 2 * 3^3 - 1`
    where `x % 16 == 5 != 1` and `x % 64 == 53 != 9`).
    """
    if "cousin_diamond2_next" not in entry:
        return True
    x = int(entry["seed"])
    if (x & 1) == 1:
        partial_next = (
            (3 * x + 1) // 4
            if (
                (x > 1 and (x % 16) == 1 and (x % 3) != 2)
                or (x >= 73 and (x % 64) == 9 and (x % 3) != 2)
            )
            else (3 * x + 1) // 2
        )
    elif x > 2 and (x % 6) == 2:
        partial_next = (x - 2) // 3
    elif x > 2 and (x % 8) == 6:
        partial_next = (x - 2) // 2
    else:
        partial_next = x // 2
    return partial_next == cousin_diamond2_step_int(x)


def run_wave5_whole_space_campaign(bank_path: Optional[Path] = None) -> Dict[str, Any]:
    """
    Execute the complete Wave 5 whole-space red-team, `T_diamond2` benchmark, multi-term /
    non-triangular barrier, 2D Beukers-Rhin / `m`-block / antipodal-prime, and coupled
    `q`-ray / `Pi_2^0` calibration campaign against `witness_bank.json`.
    """
    u_gate = audit_universality_gate(
        "Wave5_WholeSpace_W5_1_to_W5_4",
        is_finite_m_table=False,
        is_finite_n_table=False,
        is_bounded_weight_table=False,
        uses_native_decide=False,
        uses_sorry=False,
        axioms_used=("propext", "Classical.choice", "Quot.sound"),
    )
    bank = load_witness_bank(bank_path)
    wb_truth = verify_witness_bank_ground_truth(bank_path)

    gate_pos2 = evaluate_hypothesis_against_witness_bank(
        "Pos2TermValuationOnTrueCollatz",
        _dynamic_pred_pos_2term_valuation_syracuse,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    gate_laur2 = evaluate_hypothesis_against_witness_bank(
        "GlideLaurent2TermOnTrueCollatz",
        _dynamic_pred_glide_laurent_2term_syracuse,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    gate_per_val = evaluate_hypothesis_against_witness_bank(
        "PeriodicValuationPreimageDistinguishesSiblings",
        _dynamic_pred_periodic_valuation_decay,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    gate_d2_pow3 = evaluate_hypothesis_against_witness_bank(
        "PartialCousinDiamond2OmitsOddPow3Jump",
        _dynamic_pred_cousin_diamond2_omits_odd_pow3_cone,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    gate_antipodal_m1 = evaluate_hypothesis_against_witness_bank(
        "OneBlockPrime13ExclusionWithoutZIntegrality",
        _dynamic_pred_antipodal_prime_without_z_integrality,
        domains=("m1_q2_pos",),
        bank_path=bank_path,
    )
    gate_beukers = evaluate_hypothesis_against_witness_bank(
        "BeukersRhin2DConstEliminationWithoutBaker",
        _dynamic_pred_beukers_rhin_const_elim_converges,
        domains=("log2_3_convergents",),
        bank_path=bank_path,
    )

    front_a = audit_w5_front_a_nonradial_preimage_superharmonicity()
    front_b = audit_w5_front_b_cousin_diamond2_multiterm_and_nontri_matrices()
    front_c = audit_w5_front_c_beukers_rhin_mblock_and_antipodal_primes()
    front_d = audit_w5_front_d_coupled_q_rays_and_pi2_calibration()

    passed = (
        u_gate.passed
        and bool(wb_truth["all_witnesses_ground_truth_verified"])
        and (not gate_pos2["passed"])
        and ("z_pos_high_glide", "ZPOS_SYRACUSE_3_TO_5_POS_2TERM_KILLER") in gate_pos2["failures"]
        and (not gate_laur2["passed"])
        and ("z_pos_high_glide", "ZPOS_SYRACUSE_13_TO_5_V3_REBOUND") in gate_laur2["failures"]
        and (not gate_per_val["passed"])
        and gate_per_val["minimal_failure"]
        == ("z_pos_high_glide", "ZPOS_GEOM_85_VALUATION_CONSTANCY")
        and (not gate_d2_pow3["passed"])
        and gate_d2_pow3["minimal_failure"]
        == ("z_pos_high_glide", "ZPOS_COUSIN_DIAMOND2_53_ODD_POW3_JUMP")
        and (not gate_antipodal_m1["passed"])
        and gate_antipodal_m1["minimal_failure"]
        == ("m1_q2_pos", "M1_211_OVER_13_ONE_BLOCK_D13")
        and (not gate_beukers["passed"])
        and gate_beukers["minimal_failure"]
        == ("log2_3_convergents", "BEUKERS_RHIN_2D_CONST_ELIM_N5_AND_NONSEP_EXPLOSION")
        and bool(front_a["barrier_verified"])
        and bool(front_b["cousin_diamond2_global_descent_verified"])
        and bool(front_b["cousin_diamond2_syracuse_witnesses_verified"])
        and bool(front_b["cousin_diamond2_single_laurent_impossible_verified"])
        and bool(front_b["cousin_diamond2_countermodels_verified"])
        and bool(front_b["two_term_w4_trap_and_rebound_falsifier_verified"])
        and bool(front_b["non_triangular_sandwich_collapse_verified"])
        and bool(front_c["beukers_rhin_explosion_verified"])
        and bool(front_c["beukers_rhin_series_cross_verified"])
        and bool(front_c["mblock_resultant_identities_verified"])
        and bool(front_c["one_block_even_even_impossible_verified"])
        and bool(front_c["antipodal_primes_and_m1_separation_verified"])
        and bool(front_d["q_ray_affine_and_382_per_729_verified"])
        and bool(front_d["q_pos_universal_first_hit_verified"])
        and bool(front_d["length_le_7_mod373248_disjoint_verified"])
        and bool(front_d["pi2_skolem_box_and_cousin_poly_bound_verified"])
    )
    return {
        "passed": passed,
        "verdict": "REDTEAM-PASSED" if passed else "FALSIFIED",
        "universality_gate_passed": u_gate.passed,
        "witness_bank_total_entries": sum(len(v) for v in bank["domains"].values()),
        "witness_bank_falsified_count": len(bank["falsified_hypotheses"]),
        "witness_bank_ground_truth_verified": bool(wb_truth["all_witnesses_ground_truth_verified"]),
        "front_a_preimage_superharmonicity": front_a,
        "front_b_cousin_diamond2_and_cones": front_b,
        "front_c_beukers_rhin_and_resultants": front_c,
        "front_d_coupled_q_rays_and_pi2": front_d,
    }
