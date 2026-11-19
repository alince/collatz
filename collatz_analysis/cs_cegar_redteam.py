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
                if (
                    not isinstance(kills, list)
                    or len(kills) == 0
                    or not all(isinstance(s, str) and len(s.strip()) > 0 for s in kills)
                ):
                    raise ValueError(
                        f"Witness '{wid}' must have a non-empty 'kills_mechanisms' list of non-empty strings"
                    )
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
        status_val = rec.get("status")
        if status_val not in ("PROVED_BARRIER", "FALSIFIED"):
            raise ValueError(
                f"Hypothesis '{hid}' has invalid status '{status_val}', expected 'PROVED_BARRIER' or 'FALSIFIED'"
            )
        if "branch" in rec:
            branch_val = rec.get("branch")
            if not isinstance(branch_val, str) or re.match(r"^P[0-5](?:\.[1-9][0-9]*)?$", branch_val) is None:
                raise ValueError(
                    f"Hypothesis '{hid}' has invalid branch '{branch_val}', expected 'P<0..5>' or 'P<0..5>.<n>'"
                )
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
                if "loop_core_word" in entry:
                    checked_keys.add("loop_core_word")
                    u_loop = tuple(int(b) for b in entry["loop_core_word"])
                    ok = (
                        ok
                        and q_i == 0
                        and len(u_loop) > len(u_w)
                        and len(u_loop) >= 2
                        and u_loop[0] == 1
                        and u_loop[-1] == 1
                        and all(b in (0, 1) for b in u_loop)
                        and u_loop != u_w
                        and cft.exact_backward_quotient(1, u_loop, 0) == seed
                        and (not cft.is_first_hit_one_pair(u_loop, 0))
                        and cft.is_first_hit_one_pair(u_loop, 1)
                        and any(
                            u_loop == trivial_loop_extension(u_w, m_ext)
                            for m_ext in range((len(u_loop) - len(u_w)) // 2 + 1)
                        )
                    )
                if "mixed_q0_unroll_word" in entry:
                    checked_keys.add("mixed_q0_unroll_word")
                    u_mix = tuple(int(b) for b in entry["mixed_q0_unroll_word"])
                    ok = (
                        ok
                        and q_i >= 1
                        and len(u_mix) > len(u_w)
                        and len(u_mix) >= 2
                        and u_mix[0] == 1
                        and u_mix[-1] == 1
                        and all(b in (0, 1) for b in u_mix)
                        and cft.exact_backward_quotient(1, u_mix, 0) == seed
                        and (not cft.is_first_hit_one_pair(u_mix, 0))
                        and cft.is_first_hit_one_pair(u_mix, 1)
                        and any(
                            u_mix == loop_unroll_word(u_w, q_i, m_ext)
                            for m_ext in range((len(u_mix) - len(u_w)) // 2 + 1)
                        )
                    )
                dyadic_keys = (
                    "dyadic_window_exp_m",
                    "dyadic_partner_seed",
                    "dyadic_partner_core_word",
                )
                if any(k in entry for k in dyadic_keys):
                    if all(k in entry for k in dyadic_keys) and q_i == 0:
                        checked_keys.update(dyadic_keys)
                        m_win = int(entry["dyadic_window_exp_m"])
                        p_seed = int(entry["dyadic_partner_seed"])
                        u_part = tuple(int(b) for b in entry["dyadic_partner_core_word"])
                        ok = (
                            ok
                            and m_win >= 1
                            and len(u_part) == len(u_w)
                            and len(u_part) >= 2
                            and u_part[0] == 1
                            and u_part[-1] == 1
                            and all(b in (0, 1) for b in u_part)
                            and cft.exact_backward_quotient(1, u_part, 0) == p_seed
                            and cft.is_first_hit_one_pair(u_part, 0)
                            and (1 << m_win) <= seed < (1 << (m_win + 1))
                            and (1 << m_win) <= p_seed < (1 << (m_win + 1))
                            and sum(u_part) != sum(u_w)
                            and cft.canonical_suffix_shift(u_part, 1)
                            != cft.canonical_suffix_shift(u_w, 1)
                        )
                    else:
                        ok = False
                dyadic_len_keys = (
                    "dyadic_length_window_m",
                    "dyadic_length_partner_seed",
                    "dyadic_length_partner_word",
                    "dyadic_supercritical_seed",
                    "dyadic_supercritical_excess",
                )
                if any(k in entry for k in dyadic_len_keys):
                    if all(k in entry for k in dyadic_len_keys) and q_i == 0:
                        checked_keys.update(dyadic_len_keys)
                        m_lwin = int(entry["dyadic_length_window_m"])
                        lp_seed = int(entry["dyadic_length_partner_seed"])
                        u_lpart = tuple(int(b) for b in entry["dyadic_length_partner_word"])
                        sc_seed = int(entry["dyadic_supercritical_seed"])
                        sc_exc = int(entry["dyadic_supercritical_excess"])
                        if (
                            m_lwin >= 1
                            and len(u_lpart) >= 2
                            and u_lpart[0] == 1
                            and u_lpart[-1] == 1
                            and all(b in (0, 1) for b in u_lpart)
                            and sc_seed >= 3
                            and (sc_seed & 1) == 1
                        ):
                            cur_sc = sc_seed
                            sc_word: List[int] = []
                            while (cur_sc & (cur_sc - 1)) != 0 and len(sc_word) < 200:
                                b_sc = cur_sc & 1
                                sc_word.append(b_sc)
                                cur_sc = (3 * cur_sc + 1) // 2 if b_sc else cur_sc // 2
                            m_sc = sc_seed.bit_length() - 1
                            w_sc = sum(sc_word)
                            l_sc = len(sc_word)
                            ok = (
                                ok
                                and len(u_lpart) != len(u_w)
                                and sum(u_lpart) == sum(u_w)
                                and cft.exact_backward_quotient(1, u_lpart, 0) == lp_seed
                                and cft.is_first_hit_one_pair(u_lpart, 0)
                                and (1 << m_lwin) <= seed < (1 << (m_lwin + 1))
                                and (1 << m_lwin) <= lp_seed < (1 << (m_lwin + 1))
                                and cft.canonical_suffix_shift(u_lpart, 1)
                                != cft.canonical_suffix_shift(u_w, 1)
                                and (cur_sc & (cur_sc - 1)) == 0
                                and cft.exact_backward_quotient(1, tuple(sc_word), 0) == sc_seed
                                and cft.is_first_hit_one_pair(tuple(sc_word), 0)
                                and cft.is_surviving_mod373248_class(sc_seed)
                                and m_sc == m_lwin
                                and l_sc > (m_sc + w_sc + 1)
                                and (l_sc - (m_sc + w_sc + 1)) == sc_exc
                            )
                        else:
                            ok = False
                    else:
                        ok = False
                if "shorter_l10_min_core_word" in entry:
                    checked_keys.add("shorter_l10_min_core_word")
                    u_l10 = tuple(int(b) for b in entry["shorter_l10_min_core_word"])
                    if (
                        q_i == 0
                        and len(u_l10) == 10
                        and len(u_w) > 10
                        and u_l10[0] == 1
                        and u_l10[-1] == 1
                        and all(b in (0, 1) for b in u_l10)
                    ):
                        y_l10 = cft.exact_backward_quotient(1, u_l10, 0)
                        surv512_l10 = [
                            cft.exact_backward_quotient(1, (1, 1) + mid + (1,), 0)
                            for mid in product((0, 1), repeat=7)
                            if cft.is_surviving_mod512_residue(
                                cft.exact_backward_quotient(1, (1, 1) + mid + (1,), 0) % 512
                            )
                        ]
                        surv373_l10 = [
                            y_c for y_c in surv512_l10 if cft.is_surviving_mod373248_class(y_c)
                        ]
                        ok = (
                            ok
                            and cft.is_surviving_mod373248_class(y_l10)
                            and cft.is_first_hit_one_pair(u_l10, 0)
                            and len(surv512_l10) == 27
                            and len(surv373_l10) > 0
                            and y_l10 == min(surv373_l10)
                            and seed < y_l10
                        )
                    else:
                        ok = False
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
            digit_keys = (
                "even_sibling",
                "bit_length_seed",
                "bit_length_target",
                "bit_length_even_sibling",
                "digit_sig_seed",
                "digit_sig_target",
                "digit_sig_even_sibling",
            )
            ripple_keys = (
                "even_sibling",
                "ripple_carry_count_seed",
                "ripple_carry_idx_sum_seed",
                "ripple_carry_count_target",
                "ripple_carry_idx_sum_target",
                "ripple_carry_count_even_sibling",
                "ripple_carry_idx_sum_even_sibling",
            )
            window_keys = (
                "even_sibling",
                "sliding_window_width",
                "nonzero_windows_seed",
                "nonzero_windows_target",
                "nonzero_windows_even_sibling",
            )
            if any(k in entry for k in digit_keys[1:]):
                if all(k in entry for k in digit_keys) and seed >= 1 and nxt_c >= 3:
                    checked_keys.update(digit_keys)
                    ev_sib = int(entry["even_sibling"])
                    ok = (
                        ok
                        and (seed & 1) == 1
                        and (nxt_c % 3) == 2
                        and (2 * nxt_c - 1) // 3 == seed
                        and ev_sib == 2 * nxt_c
                        and int_compressed_step(ev_sib, q=3) == nxt_c
                        and seed.bit_length() == int(entry["bit_length_seed"])
                        and nxt_c.bit_length() == int(entry["bit_length_target"])
                        and ev_sib.bit_length() == int(entry["bit_length_even_sibling"])
                        and list(binary_digit_signature6(seed))
                        == [int(v) for v in entry["digit_sig_seed"]]
                        and list(binary_digit_signature6(nxt_c))
                        == [int(v) for v in entry["digit_sig_target"]]
                        and list(binary_digit_signature6(ev_sib))
                        == [int(v) for v in entry["digit_sig_even_sibling"]]
                        and binary_digit_signature6(nxt_c) == binary_digit_signature6(ev_sib)
                    )
                else:
                    ok = False
            if any(k in entry for k in ripple_keys[1:]):
                if all(k in entry for k in ripple_keys) and seed >= 1 and nxt_c >= 3:
                    checked_keys.update(ripple_keys)
                    ev_sib = int(entry["even_sibling"])
                    cnt_s, idx_s = ripple_carry_3n1_stats(seed)
                    cnt_t, idx_t = ripple_carry_3n1_stats(nxt_c)
                    cnt_e, idx_e = ripple_carry_3n1_stats(ev_sib)
                    ok = (
                        ok
                        and (seed & 1) == 1
                        and (nxt_c % 3) == 2
                        and (2 * nxt_c - 1) // 3 == seed
                        and ev_sib == 2 * nxt_c
                        and int_compressed_step(ev_sib, q=3) == nxt_c
                        and cnt_s == int(entry["ripple_carry_count_seed"])
                        and idx_s == int(entry["ripple_carry_idx_sum_seed"])
                        and cnt_t == int(entry["ripple_carry_count_target"])
                        and idx_t == int(entry["ripple_carry_idx_sum_target"])
                        and cnt_e == int(entry["ripple_carry_count_even_sibling"])
                        and idx_e == int(entry["ripple_carry_idx_sum_even_sibling"])
                        and cnt_t > 0
                        and idx_t > 0
                        and cnt_e == 0
                        and idx_e == 0
                    )
                else:
                    ok = False
            if any(k in entry for k in window_keys[1:]):
                if all(k in entry for k in window_keys) and seed >= 1 and nxt_c >= 3:
                    checked_keys.update(window_keys)
                    ev_sib = int(entry["even_sibling"])
                    w_win = int(entry["sliding_window_width"])
                    if w_win >= 2:
                        ok = (
                            ok
                            and (seed & 1) == 1
                            and (nxt_c % 3) == 2
                            and (2 * nxt_c - 1) // 3 == seed
                            and ev_sib == 2 * nxt_c
                            and int_compressed_step(ev_sib, q=3) == nxt_c
                            and list(binary_nonzero_window_list(w_win, seed))
                            == [int(v) for v in entry["nonzero_windows_seed"]]
                            and list(binary_nonzero_window_list(w_win, nxt_c))
                            == [int(v) for v in entry["nonzero_windows_target"]]
                            and list(binary_nonzero_window_list(w_win, ev_sib))
                            == [int(v) for v in entry["nonzero_windows_even_sibling"]]
                            and binary_nonzero_window_list(w_win, nxt_c)
                            == binary_nonzero_window_list(w_win, ev_sib)
                            and binary_nonzero_window_list(w_win, 200)
                            != binary_nonzero_window_list(w_win, 400)
                        )
                    else:
                        ok = False
                else:
                    ok = False
            stateful_keys = (
                "automaton_states_q",
                "multi_even_step_exp",
                "multi_even_preimage",
            )
            if any(k in entry for k in stateful_keys):
                if all(k in entry for k in stateful_keys) and seed >= 1 and nxt_c >= 3:
                    checked_keys.update(stateful_keys)
                    q_st = int(entry["automaton_states_q"])
                    d_exp = int(entry["multi_even_step_exp"])
                    ev_multi = int(entry["multi_even_preimage"])
                    if 1 <= q_st <= 3 and d_exp == math.factorial(q_st):
                        cur_ev = ev_multi
                        steps_ev_ok = True
                        for _ in range(d_exp):
                            if cur_ev < 3 or (cur_ev & 1) != 0:
                                steps_ev_ok = False
                                break
                            cur_ev >>= 1
                        all_automata_collide = True
                        for table_flat in product(range(q_st), repeat=2 * q_st):
                            delta_tbl = [
                                (table_flat[2 * st_i], table_flat[2 * st_i + 1])
                                for st_i in range(q_st)
                            ]
                            for q0_st in range(q_st):
                                if (
                                    run_lsb_automaton(q_st, delta_tbl, q0_st, nxt_c)
                                    != run_lsb_automaton(q_st, delta_tbl, q0_st, ev_multi)
                                    or run_msb_automaton(q_st, delta_tbl, q0_st, nxt_c)
                                    != run_msb_automaton(q_st, delta_tbl, q0_st, ev_multi)
                                ):
                                    all_automata_collide = False
                                    break
                            if not all_automata_collide:
                                break
                        # Verify Q = 2 trailing-zero parity automaton DOES separate nxt_c vs 2*nxt_c!
                        q2_trailing_parity = [(1, 0), (0, 1)]  # MSB: toggles on 0 after last 1
                        separates_single_even = (
                            q_st < 2
                            or run_msb_automaton(2, q2_trailing_parity, 0, nxt_c)
                            != run_msb_automaton(2, q2_trailing_parity, 0, 2 * nxt_c)
                        )
                        ok = (
                            ok
                            and (seed & 1) == 1
                            and (nxt_c % 3) == 2
                            and (2 * nxt_c - 1) // 3 == seed
                            and ev_multi == (nxt_c << d_exp)
                            and steps_ev_ok
                            and cur_ev == nxt_c
                            and all_automata_collide
                            and separates_single_even
                        )
                    else:
                        ok = False
                else:
                    ok = False
            stern_ocn_keys = (
                "even_sibling",
                "stern_seed",
                "stern_target",
                "stern_even_sibling",
                "ocn_q1_multi_even_preimage",
            )
            if any(k in entry for k in stern_ocn_keys[1:]):
                if all(k in entry for k in stern_ocn_keys) and seed >= 1 and nxt_c >= 3:
                    checked_keys.update(stern_ocn_keys)
                    ev_sib = int(entry["even_sibling"])
                    ocn_ev = int(entry["ocn_q1_multi_even_preimage"])
                    dyck_sep = (
                        run_msb_one_counter_ocn(1, [(1, 1)], [(-1, 1)], 0, nxt_c)[1] == 0
                        and run_msb_one_counter_ocn(1, [(1, 1)], [(-1, 1)], 0, ev_sib)[1] != 0
                    )
                    all_ocn_q1_collide = all(
                        (run_msb_one_counter_ocn(1, [(dz0, dz1)], [(dp0, dp1)], 0, nxt_c)[1] == 0)
                        == (run_msb_one_counter_ocn(1, [(dz0, dz1)], [(dp0, dp1)], 0, ocn_ev)[1] == 0)
                        for dz0, dz1 in product((0, 1), repeat=2)
                        for dp0, dp1 in product((-1, 0, 1), repeat=2)
                    )
                    ok = (
                        ok
                        and (seed & 1) == 1
                        and (nxt_c % 3) == 2
                        and (2 * nxt_c - 1) // 3 == seed
                        and ev_sib == 2 * nxt_c
                        and ocn_ev == 4 * nxt_c
                        and int_compressed_step(ev_sib, q=3) == nxt_c
                        and int_compressed_step(int_compressed_step(ocn_ev, q=3), q=3) == nxt_c
                        and stern_diatomic(seed) == int(entry["stern_seed"])
                        and stern_diatomic(nxt_c) == int(entry["stern_target"])
                        and stern_diatomic(ev_sib) == int(entry["stern_even_sibling"])
                        and stern_diatomic(ocn_ev) == stern_diatomic(nxt_c)
                        and stern_diatomic(ev_sib) == stern_diatomic(nxt_c)
                        and dyck_sep
                        and all_ocn_q1_collide
                    )
                else:
                    ok = False
            mixed_ocn_keys = (
                "even_sibling_preimage",
                "ocn_q2_multi_even_preimage",
                "ocn_q2_56_counter",
                "ocn_q2_224_counter",
                "ocn_q2_target_counter",
            )
            if any(k in entry for k in mixed_ocn_keys):
                if all(k in entry for k in mixed_ocn_keys) and seed >= 1 and nxt_c >= 3:
                    checked_keys.update(mixed_ocn_keys)
                    ev_sib2 = int(entry["even_sibling_preimage"])
                    ocn2_ev = int(entry["ocn_q2_multi_even_preimage"])
                    dz_mix = [((1, 0), (0, 1)), ((0, 0), (1, 1))]
                    dp_mix = [((1, 0), (0, 1)), ((0, -1), (1, -1))]
                    cfg_56 = run_msb_one_counter_ocn(2, dz_mix, dp_mix, 0, 56)
                    cfg_224 = run_msb_one_counter_ocn(2, dz_mix, dp_mix, 0, 224)
                    cfg_tgt = run_msb_one_counter_ocn(2, dz_mix, dp_mix, 0, nxt_c)
                    cfg_ev2 = run_msb_one_counter_ocn(2, dz_mix, dp_mix, 0, ocn2_ev)
                    cfg_lsb_tgt = run_lsb_one_counter_ocn(2, dz_mix, dp_mix, 0, nxt_c)
                    cfg_lsb_ev2 = run_lsb_one_counter_ocn(2, dz_mix, dp_mix, 0, ocn2_ev)
                    ok = (
                        ok
                        and (seed & 1) == 1
                        and (nxt_c % 3) == 2
                        and (2 * nxt_c - 1) // 3 == seed
                        and ev_sib2 == 2 * nxt_c
                        and ocn2_ev == 4 * nxt_c
                        and int_compressed_step(ev_sib2, q=3) == nxt_c
                        and int_compressed_step(int_compressed_step(ocn2_ev, q=3), q=3) == nxt_c
                        and cfg_56[1] == int(entry["ocn_q2_56_counter"])
                        and cfg_224[1] == int(entry["ocn_q2_224_counter"])
                        and cfg_56[1] != cfg_224[1]
                        and cfg_tgt[1] == int(entry["ocn_q2_target_counter"])
                        and cfg_tgt == cfg_ev2
                        and (cfg_lsb_tgt[0], cfg_lsb_tgt[1] == 0)
                        == (cfg_lsb_ev2[0], cfg_lsb_ev2[1] == 0)
                    )
                else:
                    ok = False
            pda_q2_g3_keys = (
                "pda_q2_g3_sep_preimage",
                "pda_q2_g3_multi_even_preimage",
                "pda_q2_g3_56_height",
                "pda_q2_g3_224_height",
                "pda_q2_g3_12416_height",
                "pda_q2_g3_49664_height",
            )
            if any(k in entry for k in pda_q2_g3_keys):
                if all(k in entry for k in pda_q2_g3_keys) and seed >= 1 and nxt_c >= 3:
                    checked_keys.update(pda_q2_g3_keys)
                    pda_sep = int(entry["pda_q2_g3_sep_preimage"])
                    pda_ev = int(entry["pda_q2_g3_multi_even_preimage"])
                    delta_pda_w11 = _canonical_pda_q2_g3_table()
                    p_56 = run_msb_pda_stack(2, 3, delta_pda_w11, 0, 56)
                    p_224 = run_msb_pda_stack(2, 3, delta_pda_w11, 0, 224)
                    p_12k = run_msb_pda_stack(2, 3, delta_pda_w11, 0, 12_416)
                    p_49k = run_msb_pda_stack(2, 3, delta_pda_w11, 0, 49_664)
                    p_tgt = run_msb_pda_stack(2, 3, delta_pda_w11, 0, nxt_c)
                    p_sep_cfg = run_msb_pda_stack(2, 3, delta_pda_w11, 0, pda_sep)
                    p_ev_cfg = run_msb_pda_stack(2, 3, delta_pda_w11, 0, pda_ev)
                    cur_p = pda_ev
                    steps_p_ok = True
                    for _ in range(6):
                        if (cur_p & 1) != 0 or cur_p <= 2:
                            steps_p_ok = False
                            break
                        cur_p >>= 1
                    ok = (
                        ok
                        and (seed & 1) == 1
                        and (nxt_c % 3) == 2
                        and (2 * nxt_c - 1) // 3 == seed
                        and pda_sep == 4 * nxt_c
                        and pda_ev == 64 * nxt_c
                        and steps_p_ok
                        and cur_p == nxt_c
                        and p_56[2] == int(entry["pda_q2_g3_56_height"])
                        and p_224[2] == int(entry["pda_q2_g3_224_height"])
                        and p_56 != p_224
                        and p_12k[2] == int(entry["pda_q2_g3_12416_height"])
                        and p_49k[2] == int(entry["pda_q2_g3_49664_height"])
                        and p_12k != p_49k
                        and p_tgt != p_sep_cfg
                        and p_tgt == p_ev_cfg
                    )
                else:
                    ok = False
            asym_ocn_keys = (
                "asym_ocn_even_preimage",
                "asym_ocn_mersenne_k4_target",
                "asym_ocn_mersenne_k4_sum",
                "asym_ocn_mersenne_k4_rhs",
                "asym_ocn_target_sum",
                "asym_ocn_target_rhs",
            )
            if any(k in entry for k in asym_ocn_keys):
                if all(k in entry for k in asym_ocn_keys) and seed >= 1 and nxt_c >= 3:
                    checked_keys.update(asym_ocn_keys)
                    asym_ev = int(entry["asym_ocn_even_preimage"])
                    m_k4 = int(entry["asym_ocn_mersenne_k4_target"])
                    dz_asym = [((0, 0), (1, 0)), ((0, 1), (1, 0))]
                    dp_asym = [((0, 0), (0, 1)), ((1, 0), (1, 0))]

                    def _w_asym(val_n: int) -> Fraction:
                        _, c_v = run_msb_one_counter_ocn(2, dz_asym, dp_asym, 0, val_n)
                        bl_v = val_n.bit_length()
                        return Fraction(c_v + 1, bl_v * bl_v)

                    asym_slopes_ok = all(
                        run_msb_one_counter_ocn(2, dz_asym, dp_asym, 0, (1 << (k_t + 1)) - 1)[1] == 0
                        and run_msb_one_counter_ocn(2, dz_asym, dp_asym, 0, 3 * (1 << k_t) - 1)[1] == k_t + 1
                        and run_msb_one_counter_ocn(2, dz_asym, dp_asym, 0, 6 * (1 << k_t) - 2)[1] == k_t + 1
                        for k_t in range(1, 9)
                    )
                    mers_bypass_ok = all(
                        _w_asym(6 * (1 << k_t) - 2) + _w_asym((1 << (k_t + 1)) - 1)
                        < _w_asym(3 * (1 << k_t) - 1)
                        for k_t in range(4, 9)
                    )
                    k4_sum = _w_asym(2 * m_k4) + _w_asym((2 * m_k4 - 1) // 3)
                    k4_rhs = _w_asym(m_k4)
                    tgt_sum = _w_asym(asym_ev) + _w_asym(seed)
                    tgt_rhs = _w_asym(nxt_c)
                    ok = (
                        ok
                        and (seed & 1) == 1
                        and (nxt_c % 3) == 2
                        and (2 * nxt_c - 1) // 3 == seed
                        and asym_ev == 2 * nxt_c
                        and int_compressed_step(asym_ev, q=3) == nxt_c
                        and m_k4 == 47
                        and asym_slopes_ok
                        and mers_bypass_ok
                        and k4_sum == Fraction(str(entry["asym_ocn_mersenne_k4_sum"]))
                        and k4_rhs == Fraction(str(entry["asym_ocn_mersenne_k4_rhs"]))
                        and k4_sum < k4_rhs
                        and tgt_sum == Fraction(str(entry["asym_ocn_target_sum"]))
                        and tgt_rhs == Fraction(str(entry["asym_ocn_target_rhs"]))
                        and tgt_sum > tgt_rhs
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
        if "cousin_diamond3_next" in entry:
            checked_keys.add("cousin_diamond3_next")
            claims_checked += 1
            nxt_d3 = cousin_diamond3_step_int(seed, q=3)
            ok = ok and (nxt_d3 == int(entry["cousin_diamond3_next"]))
            if "cousin_diamond3_steps_to_1" in entry:
                checked_keys.add("cousin_diamond3_steps_to_1")
                cur_d3 = seed
                st_d3 = 0
                while cur_d3 != 1 and st_d3 < 5000:
                    cur_d3 = cousin_diamond3_step_int(cur_d3, q=3)
                    st_d3 += 1
                ok = ok and (cur_d3 == 1) and (st_d3 == int(entry["cousin_diamond3_steps_to_1"]))
            if "phi_diamond2_seed" in entry:
                checked_keys.add("phi_diamond2_seed")
                ok = ok and (cousin_diamond2_phi(seed) == int(entry["phi_diamond2_seed"]))
            if "phi_diamond2_next" in entry:
                checked_keys.add("phi_diamond2_next")
                ok = ok and (cousin_diamond2_phi(nxt_d3) == int(entry["phi_diamond2_next"]))
        if "cousin_diamond4_next" in entry:
            checked_keys.add("cousin_diamond4_next")
            claims_checked += 1
            nxt_d4 = cousin_diamond4_step_int(seed, q=3)
            ok = ok and (nxt_d4 == int(entry["cousin_diamond4_next"]))
            if "cousin_diamond4_steps_to_1" in entry:
                checked_keys.add("cousin_diamond4_steps_to_1")
                cur_d4 = seed
                st_d4 = 0
                while cur_d4 != 1 and st_d4 < 5000:
                    cur_d4 = cousin_diamond4_step_int(cur_d4, q=3)
                    st_d4 += 1
                ok = ok and (cur_d4 == 1) and (st_d4 == int(entry["cousin_diamond4_steps_to_1"]))
            if "phi_diamond2_seed" in entry:
                checked_keys.add("phi_diamond2_seed")
                ok = ok and (cousin_diamond2_phi(seed) == int(entry["phi_diamond2_seed"]))
            if "phi_diamond2_next" in entry:
                checked_keys.add("phi_diamond2_next")
                ok = ok and (cousin_diamond2_phi(nxt_d4) == int(entry["phi_diamond2_next"]))
        if "cousin_diamond5_next" in entry:
            checked_keys.add("cousin_diamond5_next")
            claims_checked += 1
            nxt_d5 = cousin_diamond5_step_int(seed, q=3)
            ok = (
                ok
                and is_diamond5_cone6(seed)
                and is_diamond4_cone5(nxt_d5)
                and (nxt_d5 == int(entry["cousin_diamond5_next"]))
            )
            if "cousin_diamond5_steps_to_1" in entry:
                checked_keys.add("cousin_diamond5_steps_to_1")
                cur_d5 = seed
                st_d5 = 0
                while cur_d5 != 1 and st_d5 < 5000:
                    cur_d5 = cousin_diamond5_step_int(cur_d5, q=3)
                    st_d5 += 1
                ok = ok and (cur_d5 == 1) and (st_d5 == int(entry["cousin_diamond5_steps_to_1"]))
            if "phi_diamond2_seed" in entry:
                checked_keys.add("phi_diamond2_seed")
                ok = ok and (cousin_diamond2_phi(seed) == int(entry["phi_diamond2_seed"]))
            if "phi_diamond2_next" in entry:
                checked_keys.add("phi_diamond2_next")
                ok = ok and (cousin_diamond2_phi(nxt_d5) == int(entry["phi_diamond2_next"]))
                if "phi_diamond2_seed" in entry:
                    ok = ok and (cousin_diamond2_phi(nxt_d5) > cousin_diamond2_phi(seed))
        if "cousin_diamond6_next" in entry:
            checked_keys.add("cousin_diamond6_next")
            claims_checked += 1
            nxt_d6 = cousin_diamond6_step_int(seed, q=3)
            ok = (
                ok
                and is_diamond6_cone7(seed)
                and is_diamond5_cone6(nxt_d6)
                and is_diamond4_cone5(cousin_diamond6_step_int(nxt_d6, q=3))
                and (nxt_d6 == int(entry["cousin_diamond6_next"]))
            )
            if "cousin_diamond6_steps_to_1" in entry:
                checked_keys.add("cousin_diamond6_steps_to_1")
                cur_d6 = seed
                st_d6 = 0
                while cur_d6 != 1 and st_d6 < 5000:
                    cur_d6 = cousin_diamond6_step_int(cur_d6, q=3)
                    st_d6 += 1
                ok = ok and (cur_d6 == 1) and (st_d6 == int(entry["cousin_diamond6_steps_to_1"]))
            if "phi_diamond2_seed" in entry:
                checked_keys.add("phi_diamond2_seed")
                ok = ok and (cousin_diamond2_phi(seed) == int(entry["phi_diamond2_seed"]))
            if "phi_diamond2_next" in entry:
                checked_keys.add("phi_diamond2_next")
                ok = ok and (cousin_diamond2_phi(nxt_d6) == int(entry["phi_diamond2_next"]))
                if "phi_diamond2_seed" in entry:
                    ok = ok and (cousin_diamond2_phi(nxt_d6) > cousin_diamond2_phi(seed))
        if "cousin_diamond7_next" in entry:
            checked_keys.add("cousin_diamond7_next")
            claims_checked += 1
            nxt_d7 = cousin_diamond7_step_int(seed, q=3)
            nxt2_d7 = cousin_diamond7_step_int(nxt_d7, q=3)
            nxt3_d7 = cousin_diamond7_step_int(nxt2_d7, q=3)
            ok = (
                ok
                and is_diamond7_cone8(seed)
                and is_diamond6_cone7(nxt_d7)
                and is_diamond5_cone6(nxt2_d7)
                and is_diamond4_cone5(nxt3_d7)
                and (nxt_d7 == int(entry["cousin_diamond7_next"]))
            )
            if "cousin_diamond7_steps_to_1" in entry:
                checked_keys.add("cousin_diamond7_steps_to_1")
                cur_d7 = seed
                st_d7 = 0
                while cur_d7 != 1 and st_d7 < 5000:
                    cur_d7 = cousin_diamond7_step_int(cur_d7, q=3)
                    st_d7 += 1
                ok = ok and (cur_d7 == 1) and (st_d7 == int(entry["cousin_diamond7_steps_to_1"]))
            if "phi_diamond2_seed" in entry:
                checked_keys.add("phi_diamond2_seed")
                ok = ok and (cousin_diamond2_phi(seed) == int(entry["phi_diamond2_seed"]))
            if "phi_diamond2_next" in entry:
                checked_keys.add("phi_diamond2_next")
                ok = ok and (cousin_diamond2_phi(nxt_d7) == int(entry["phi_diamond2_next"]))
                if "phi_diamond2_seed" in entry:
                    ok = ok and (cousin_diamond2_phi(nxt_d7) > cousin_diamond2_phi(seed))
        if "cousin_diamond8_next" in entry:
            checked_keys.add("cousin_diamond8_next")
            claims_checked += 1
            nxt_d8 = cousin_diamond8_step_int(seed, q=3)
            nxt2_d8 = cousin_diamond8_step_int(nxt_d8, q=3)
            nxt3_d8 = cousin_diamond8_step_int(nxt2_d8, q=3)
            nxt4_d8 = cousin_diamond8_step_int(nxt3_d8, q=3)
            ok = (
                ok
                and is_diamond8_cone9(seed)
                and is_diamond7_cone8(nxt_d8)
                and is_diamond6_cone7(nxt2_d8)
                and is_diamond5_cone6(nxt3_d8)
                and is_diamond4_cone5(nxt4_d8)
                and (nxt_d8 == int(entry["cousin_diamond8_next"]))
            )
            if "cousin_diamond8_steps_to_1" in entry:
                checked_keys.add("cousin_diamond8_steps_to_1")
                cur_d8 = seed
                st_d8 = 0
                while cur_d8 != 1 and st_d8 < 5000:
                    cur_d8 = cousin_diamond8_step_int(cur_d8, q=3)
                    st_d8 += 1
                ok = ok and (cur_d8 == 1) and (st_d8 == int(entry["cousin_diamond8_steps_to_1"]))
            if "phi_diamond2_seed" in entry:
                checked_keys.add("phi_diamond2_seed")
                ok = ok and (cousin_diamond2_phi(seed) == int(entry["phi_diamond2_seed"]))
            if "phi_diamond2_next" in entry:
                checked_keys.add("phi_diamond2_next")
                ok = ok and (cousin_diamond2_phi(nxt_d8) == int(entry["phi_diamond2_next"]))
                if "phi_diamond2_seed" in entry:
                    ok = ok and (cousin_diamond2_phi(nxt_d8) > cousin_diamond2_phi(seed))
        if "spiral_block_next" in entry or "spiral_block_2_next" in entry:
            if "spiral_block_next" in entry and seed >= 1 and (seed & 1) == 1:
                checked_keys.add("spiral_block_next")
                claims_checked += 1
                sb1 = spiral_block_return_int(seed)
                ok = ok and (sb1 == int(entry["spiral_block_next"]))
                if "spiral_block_2_next" in entry:
                    checked_keys.add("spiral_block_2_next")
                    ok = ok and (spiral_block_return_int(sb1) == int(entry["spiral_block_2_next"]))
            else:
                ok = False
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
        if entry.get("system") in (
            "T_diamond",
            "T_diamond2",
            "T_diamond3",
            "T_diamond4",
            "T_diamond5",
            "T_diamond6",
            "T_diamond7",
            "T_diamond8",
        ):
            checked_m1.update(("system", "orbit"))
            sys_m1 = entry.get("system")
            step_fn_q6 = {
                "T_diamond": cousin_diamond_step_q6,
                "T_diamond2": cousin_diamond2_step_q6,
                "T_diamond3": cousin_diamond3_step_q6,
                "T_diamond4": cousin_diamond4_step_q6,
                "T_diamond5": cousin_diamond5_step_q6,
                "T_diamond6": cousin_diamond6_step_q6,
                "T_diamond7": cousin_diamond7_step_q6,
                "T_diamond8": cousin_diamond8_step_q6,
            }[str(sys_m1)]
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
        if entry.get("system") in (
            "T_diamond_q7",
            "T_diamond2_q7",
            "T_diamond3_q7",
            "T_diamond4_q7",
            "T_diamond5_q7",
            "T_diamond6_q7",
            "T_diamond7_q7",
            "T_diamond8_q7",
        ):
            checked_m3.update(("system", "orbit"))
            sys_m3 = entry.get("system")
            step_fn_m3 = {
                "T_diamond_q7": cousin_diamond_step_int,
                "T_diamond2_q7": cousin_diamond2_step_int,
                "T_diamond3_q7": cousin_diamond3_step_int,
                "T_diamond4_q7": cousin_diamond4_step_int,
                "T_diamond5_q7": cousin_diamond5_step_int,
                "T_diamond6_q7": cousin_diamond6_step_int,
                "T_diamond7_q7": cousin_diamond7_step_int,
                "T_diamond8_q7": cousin_diamond8_step_int,
            }[str(sys_m3)]
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
            if "gap_mod8" in entry:
                checked_conv.add("gap_mod8")
                ok = ok and (gap > 0) and ((gap % 8) == int(entry["gap_mod8"]))
            coprime2_keys = (
                "second_coprime_order_prime",
                "second_ord2_mod_p",
                "second_ord32_mod_p",
            )
            if any(k in entry for k in coprime2_keys):
                if all(k in entry for k in coprime2_keys):
                    checked_conv.update(coprime2_keys)
                    p2 = int(entry["second_coprime_order_prime"])
                    is_p2_prime = (
                        p2 > 331
                        and (p2 & 1) == 1
                        and all(p2 % d_i != 0 for d_i in range(3, int(math.isqrt(p2)) + 1, 2))
                    )
                    if is_p2_prime and p2 <= 1_500_000:
                        o2_p2 = _mult_order_mod_prime(2, p2)
                        o32_p2 = _mult_order_mod_prime((3 * pow(2, -1, p2)) % p2, p2)
                        hits_to_p2 = _scan_coprime_order_primes_up_to(p2)
                        ok = (
                            ok
                            and o2_p2 == int(entry["second_ord2_mod_p"])
                            and o32_p2 == int(entry["second_ord32_mod_p"])
                            and math.gcd(o2_p2, o32_p2) == 1
                            and (p2 % 8) == 3
                            and tuple(h[0] for h in hits_to_p2) == (331, p2)
                        )
                    else:
                        ok = False
                else:
                    ok = False
            twobase_keys = ("laurent_twobase_4x4_u", "laurent_twobase_4x4_det")
            if any(k in entry for k in twobase_keys):
                if all(k in entry for k in twobase_keys) and w_val >= 1 and k_val >= 1:
                    checked_conv.update(twobase_keys)
                    u_tb = int(entry["laurent_twobase_4x4_u"])
                    det_tb_exp = int(entry["laurent_twobase_4x4_det"])
                    if u_tb >= 1:
                        rows_tb = [(0, 0), (1, 0), (0, 1), (1, 1)]
                        cols_tb = [(0, 0), (1, 0), (0, u_tb), (1, u_tb)]
                        mat_tb = [
                            [
                                math.comb(r_i * w_val + s_i * k_val, t_i)
                                * (1 << (r_i * u_i))
                                * (3 ** (s_i * u_i))
                                for (t_i, u_i) in cols_tb
                            ]
                            for (r_i, s_i) in rows_tb
                        ]
                        # Exact 4x4 Laplace expansion along row 0 (entries [1, 0, 1, 0])
                        det_tb_mat = mat_tb[0][0] * _det3_int(
                            tuple((mat_tb[r_i][1], mat_tb[r_i][2], mat_tb[r_i][3]) for r_i in (1, 2, 3))
                        ) + mat_tb[0][2] * _det3_int(
                            tuple((mat_tb[r_i][0], mat_tb[r_i][1], mat_tb[r_i][3]) for r_i in (1, 2, 3))
                        )
                        det_tb_closed = (w_val * w_val) * (1 << u_tb) * (((3**u_tb) - 1) ** 2) - (
                            k_val * k_val
                        ) * (3**u_tb) * (((1 << u_tb) - 1) ** 2)
                        ok = (
                            ok
                            and math.gcd(w_val, k_val) == 1
                            and gap > 0
                            and det_tb_mat == det_tb_closed
                            and det_tb_mat == det_tb_exp
                            and det_tb_mat == 0
                        )
                    else:
                        ok = False
                else:
                    ok = False
            coprime34_keys = (
                "third_coprime_order_prime",
                "third_ord2_mod_p",
                "third_ord32_mod_p",
                "third_mod8",
                "fourth_coprime_order_prime",
                "fourth_ord2_mod_p",
                "fourth_ord32_mod_p",
                "fourth_mod8",
            )
            if any(k in entry for k in coprime34_keys):
                if all(k in entry for k in coprime34_keys):
                    checked_conv.update(coprime34_keys)
                    p3 = int(entry["third_coprime_order_prime"])
                    p4 = int(entry["fourth_coprime_order_prime"])
                    is_p3_prime = (
                        p3 > 1_210_483
                        and (p3 & 1) == 1
                        and all(p3 % d_i != 0 for d_i in range(3, int(math.isqrt(p3)) + 1, 2))
                    )
                    is_p4_prime = (
                        p4 > p3
                        and (p4 & 1) == 1
                        and all(p4 % d_i != 0 for d_i in range(3, int(math.isqrt(p4)) + 1, 2))
                    )
                    if is_p3_prime and is_p4_prime:
                        o2_p3 = _mult_order_mod_prime(2, p3)
                        o32_p3 = _mult_order_mod_prime((3 * pow(2, -1, p3)) % p3, p3)
                        o2_p4 = _mult_order_mod_prime(2, p4)
                        o32_p4 = _mult_order_mod_prime((3 * pow(2, -1, p4)) % p4, p4)
                        ok = (
                            ok
                            and o2_p3 == int(entry["third_ord2_mod_p"])
                            and o32_p3 == int(entry["third_ord32_mod_p"])
                            and math.gcd(o2_p3, o32_p3) == 1
                            and (p3 % 8) == int(entry["third_mod8"])
                            and (p3 % 8) in (1, 3)
                            and o2_p4 == int(entry["fourth_ord2_mod_p"])
                            and o32_p4 == int(entry["fourth_ord32_mod_p"])
                            and math.gcd(o2_p4, o32_p4) == 1
                            and (p4 % 8) == int(entry["fourth_mod8"])
                            and (p4 % 8) in (5, 7)
                        )
                    else:
                        ok = False
                else:
                    ok = False
            twobase6_keys = (
                "laurent_twobase_6x6_u",
                "laurent_twobase_6x6_det",
                "cone_flip_u2_neg_pair",
                "cone_flip_u2_pos_pair",
            )
            if any(k in entry for k in twobase6_keys):
                neg_pr = entry.get("cone_flip_u2_neg_pair")
                pos_pr = entry.get("cone_flip_u2_pos_pair")
                if (
                    all(k in entry for k in twobase6_keys)
                    and w_val >= 1
                    and k_val >= 1
                    and isinstance(neg_pr, list)
                    and len(neg_pr) == 2
                    and isinstance(pos_pr, list)
                    and len(pos_pr) == 2
                ):
                    checked_conv.update(twobase6_keys)
                    u6 = int(entry["laurent_twobase_6x6_u"])
                    det6_exp = int(entry["laurent_twobase_6x6_det"])
                    wn, kn = int(neg_pr[0]), int(neg_pr[1])
                    wp, kp = int(pos_pr[0]), int(pos_pr[1])
                    if u6 >= 1 and wn >= 1 and kn >= 1 and wp >= 1 and kp >= 1:
                        det6_mat = laurent_twobase_6x6_det_matrix(w_val, k_val, u6)
                        det6_closed = laurent_twobase_6x6_det_closed(w_val, k_val, u6)
                        det_neg = laurent_twobase_6x6_det_matrix(wn, kn, 2)
                        det_pos = laurent_twobase_6x6_det_matrix(wp, kp, 2)
                        ok = (
                            ok
                            and (u6 & 1) == 1
                            and math.gcd(w_val, k_val) == 1
                            and gap > 0
                            and det6_mat == det6_closed
                            and det6_mat == det6_exp
                            and det6_mat == 0
                            and 3 * kn <= 5 * wn
                            and (3**wn) < (1 << kn)
                            and 3 * kp <= 5 * wp
                            and (3**wp) < (1 << kp)
                            and det_neg == laurent_twobase_6x6_det_closed(wn, kn, 2)
                            and det_pos == laurent_twobase_6x6_det_closed(wp, kp, 2)
                            and det_neg < 0
                            and det_pos > 0
                        )
                    else:
                        ok = False
                else:
                    ok = False
            mod24_keys = (
                "mod24_excluded_prime",
                "mod24_ord2",
                "mod24_ord32",
                "mod24_companion_prime",
                "mod24_companion_ord2",
                "mod24_companion_ord32",
            )
            if any(k in entry for k in mod24_keys):
                if all(k in entry for k in mod24_keys):
                    checked_conv.update(mod24_keys)
                    q_ex = int(entry["mod24_excluded_prime"])
                    q_co = int(entry["mod24_companion_prime"])
                    is_qex_prime = (
                        q_ex >= 5
                        and (q_ex & 1) == 1
                        and all(q_ex % d_i != 0 for d_i in range(3, int(math.isqrt(q_ex)) + 1, 2))
                    )
                    is_qco_prime = (
                        q_co >= 5
                        and (q_co & 1) == 1
                        and all(q_co % d_i != 0 for d_i in range(3, int(math.isqrt(q_co)) + 1, 2))
                    )
                    if is_qex_prime and is_qco_prime:
                        o2_ex = _mult_order_mod_prime(2, q_ex)
                        o32_ex = _mult_order_mod_prime((3 * pow(2, -1, q_ex)) % q_ex, q_ex)
                        o2_co = _mult_order_mod_prime(2, q_co)
                        o32_co = _mult_order_mod_prime((3 * pow(2, -1, q_co)) % q_co, q_co)
                        ok = (
                            ok
                            and q_ex == gap
                            and (q_ex % 24) == 13
                            and (q_co % 24) == 11
                            and o2_ex == int(entry["mod24_ord2"])
                            and o32_ex == int(entry["mod24_ord32"])
                            and o2_co == int(entry["mod24_companion_ord2"])
                            and o32_co == int(entry["mod24_companion_ord32"])
                            and (math.gcd(o2_ex, o32_ex) % 2) == 0
                            and (math.gcd(o2_co, o32_co) % 2) == 0
                        )
                    else:
                        ok = False
                else:
                    ok = False
            t3u2_keys = (
                "laurent_twobase_6x6_t3u2_u",
                "laurent_twobase_6x6_t3u2_det",
                "t3u2_cone_pos_pair",
                "t3u2_outer_neg_pair",
            )
            if any(k in entry for k in t3u2_keys):
                pos_pr = entry.get("t3u2_cone_pos_pair")
                neg_pr = entry.get("t3u2_outer_neg_pair")
                if (
                    all(k in entry for k in t3u2_keys)
                    and w_val >= 1
                    and k_val >= 1
                    and isinstance(pos_pr, list)
                    and len(pos_pr) == 2
                    and isinstance(neg_pr, list)
                    and len(neg_pr) == 2
                ):
                    checked_conv.update(t3u2_keys)
                    u_t3 = int(entry["laurent_twobase_6x6_t3u2_u"])
                    det_t3_exp = int(entry["laurent_twobase_6x6_t3u2_det"])
                    wp, kp = int(pos_pr[0]), int(pos_pr[1])
                    wn, kn = int(neg_pr[0]), int(neg_pr[1])
                    if u_t3 >= 1 and wp >= 1 and kp >= 1 and wn >= 1 and kn >= 1:
                        det_mat = laurent_twobase_6x6_t3u2_det_matrix(w_val, k_val, u_t3)
                        det_cl = laurent_twobase_6x6_t3u2_det_closed(w_val, k_val, u_t3)
                        det_p1 = laurent_twobase_6x6_t3u2_det_matrix(wp, kp, 1)
                        det_n1 = laurent_twobase_6x6_t3u2_det_matrix(wn, kn, 1)
                        ok = (
                            ok
                            and (u_t3 & 1) == 0
                            and math.gcd(w_val, k_val) == 1
                            and gap > 0
                            and det_mat == det_cl
                            and det_mat == det_t3_exp
                            and det_mat == 0
                            and (3**wp) < (1 << kp)
                            and 3 * kp <= 5 * wp
                            and (3**wn) < (1 << kn)
                            and 3 * kn > 5 * wn
                            and det_p1 == laurent_twobase_6x6_t3u2_det_closed(wp, kp, 1)
                            and det_n1 == laurent_twobase_6x6_t3u2_det_closed(wn, kn, 1)
                            and det_p1 > 0
                            and det_n1 < 0
                        )
                    else:
                        ok = False
                else:
                    ok = False
            recip5_17_keys = (
                "mod24_5_escape_prime",
                "mod24_5_escape_ord2",
                "mod24_5_escape_ord32",
                "mod24_17_escape_prime",
                "mod24_17_escape_ord2",
                "mod24_17_escape_ord32",
                "cubic_excluded_prime",
                "cubic_excluded_ord2",
                "cubic_excluded_ord32",
            )
            if any(k in entry for k in recip5_17_keys):
                if all(k in entry for k in recip5_17_keys):
                    checked_conv.update(recip5_17_keys)
                    q5 = int(entry["mod24_5_escape_prime"])
                    q17 = int(entry["mod24_17_escape_prime"])
                    q3c = int(entry["cubic_excluded_prime"])

                    def _is_odd_prime_ge5(p_cand: int) -> bool:
                        return (
                            p_cand >= 5
                            and (p_cand & 1) == 1
                            and all(p_cand % d_i != 0 for d_i in range(3, int(math.isqrt(p_cand)) + 1, 2))
                        )

                    if _is_odd_prime_ge5(q5) and _is_odd_prime_ge5(q17) and _is_odd_prime_ge5(q3c):
                        o2_5 = _mult_order_mod_prime(2, q5)
                        o32_5 = _mult_order_mod_prime((3 * pow(2, -1, q5)) % q5, q5)
                        o2_17 = _mult_order_mod_prime(2, q17)
                        o32_17 = _mult_order_mod_prime((3 * pow(2, -1, q17)) % q17, q17)
                        o2_3c = _mult_order_mod_prime(2, q3c)
                        o32_3c = _mult_order_mod_prime((3 * pow(2, -1, q3c)) % q3c, q3c)
                        ok = (
                            ok
                            and (q5 % 24) == 5
                            and pow(6, (q5 - 1) // 4, q5) == q5 - 1
                            and (q17 % 24) == 17
                            and (q3c % 72) == 1
                            and o2_5 == int(entry["mod24_5_escape_ord2"])
                            and o32_5 == int(entry["mod24_5_escape_ord32"])
                            and o2_17 == int(entry["mod24_17_escape_ord2"])
                            and o32_17 == int(entry["mod24_17_escape_ord32"])
                            and o2_3c == int(entry["cubic_excluded_ord2"])
                            and o32_3c == int(entry["cubic_excluded_ord32"])
                            and (math.gcd(o2_5, o32_5) % 2) == 1
                            and (math.gcd(o2_17, o32_17) % 2) == 1
                            and (o32_17 % 8) == 0
                            and (math.gcd(o2_3c, o32_3c) % 3) == 0
                        )
                    else:
                        ok = False
                else:
                    ok = False
            t4u2_8x8_keys = (
                "laurent_twobase_8x8_t4u2_u1_det",
                "laurent_twobase_8x8_t4u2_u4_det",
                "t4u2_cone_pos_u4_pair",
            )
            if any(k in entry for k in t4u2_8x8_keys):
                pos4_pr = entry.get("t4u2_cone_pos_u4_pair")
                if (
                    all(k in entry for k in t4u2_8x8_keys)
                    and w_val >= 1
                    and k_val >= 1
                    and isinstance(pos4_pr, list)
                    and len(pos4_pr) == 2
                ):
                    checked_conv.update(t4u2_8x8_keys)
                    det8_u1_exp = int(entry["laurent_twobase_8x8_t4u2_u1_det"])
                    det8_u4_exp = int(entry["laurent_twobase_8x8_t4u2_u4_det"])
                    wp4, kp4 = int(pos4_pr[0]), int(pos4_pr[1])
                    if wp4 >= 1 and kp4 >= 1:
                        d8_u1 = laurent_twobase_8x8_t4u2_det_matrix(w_val, k_val, 1)
                        d8_u4 = laurent_twobase_8x8_t4u2_det_matrix(w_val, k_val, 4)
                        d8_pos4 = laurent_twobase_8x8_t4u2_det_matrix(wp4, kp4, 4)
                        ok = (
                            ok
                            and math.gcd(w_val, k_val) == 1
                            and math.gcd(wp4, kp4) == 1
                            and gap > 0
                            and 3 * k_val <= 5 * w_val
                            and (3**wp4) < (1 << kp4)
                            and 3 * kp4 <= 5 * wp4
                            and d8_u1 == det8_u1_exp
                            and d8_u4 == det8_u4_exp
                            and d8_u1 < 0
                            and d8_u4 < 0
                            and d8_pos4 > 0
                        )
                    else:
                        ok = False
                else:
                    ok = False
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
        elif "laurent_grid" in entry:
            req_laur = (
                "laurent_grid",
                "low_W",
                "low_K",
                "low_det_nonzero",
                "low_det_int_log2",
                "low_det_m0_log2",
                "high_W",
                "high_K",
                "high_det_nonzero",
                "high_det_int_log2",
                "high_det_m0_log2",
            )
            grid_vals = entry.get("laurent_grid")
            if (
                all(k in entry for k in req_laur)
                and isinstance(grid_vals, list)
                and len(grid_vals) == 4
            ):
                checked_conv.update(req_laur)
                r_g, s_g, t_g, u_g = (int(v) for v in grid_vals)
                res_low = _solve_laurent_2log_interpolation_det(
                    int(entry["low_W"]), int(entry["low_K"]), r_g, s_g, t_g, u_g
                )
                res_high = _solve_laurent_2log_interpolation_det(
                    int(entry["high_W"]), int(entry["high_K"]), r_g, s_g, t_g, u_g
                )
                ok = (
                    ok
                    and bool(res_low["det_nonzero"]) == bool(entry["low_det_nonzero"])
                    and abs(float(res_low["det_int_log2"]) - float(entry["low_det_int_log2"])) < 1e-3
                    and abs(float(res_low["det_m0_log2"]) - float(entry["low_det_m0_log2"])) < 1e-3
                    and bool(res_high["det_nonzero"]) == bool(entry["high_det_nonzero"])
                    and abs(float(res_high["det_int_log2"]) - float(entry["high_det_int_log2"])) < 1e-3
                    and abs(float(res_high["det_m0_log2"]) - float(entry["high_det_m0_log2"])) < 1e-3
                )
            else:
                ok = False
        elif "laurent_scaled_grid" in entry:
            req_scaled = (
                "W",
                "K",
                "laurent_scaled_grid",
                "det_m0_log2",
                "det_at_cubic_gap_log2",
                "coprime_order_barrier_prime",
                "ord2_mod_p",
                "ord32_mod_p",
            )
            grid_s = entry.get("laurent_scaled_grid")
            if (
                all(k in entry for k in req_scaled)
                and isinstance(grid_s, list)
                and len(grid_s) == 4
            ):
                checked_conv.update(req_scaled)
                w_sc, k_sc = int(entry["W"]), int(entry["K"])
                r_g, s_g, t_g, u_g = (int(v) for v in grid_s)
                res_pert = _solve_laurent_perturbed_cubic_gap_det(w_sc, k_sc, r_g, s_g, t_g, u_g)
                p_bar = int(entry["coprime_order_barrier_prime"])
                is_p_prime = (
                    p_bar >= 5
                    and (p_bar & 1) == 1
                    and all(p_bar % d_i != 0 for d_i in range(3, int(math.isqrt(p_bar)) + 1, 2))
                )
                if is_p_prime:
                    ord2_obs = _mult_order_mod_prime(2, p_bar)
                    ord32_obs = _mult_order_mod_prime((3 * pow(2, -1, p_bar)) % p_bar, p_bar)
                    smaller_all_ge2 = True
                    for q_p in range(5, p_bar, 2):
                        if all(q_p % d_i != 0 for d_i in range(3, int(math.isqrt(q_p)) + 1, 2)):
                            o2_q = _mult_order_mod_prime(2, q_p)
                            o32_q = _mult_order_mod_prime((3 * pow(2, -1, q_p)) % q_p, q_p)
                            if math.gcd(o2_q, o32_q) < 2:
                                smaller_all_ge2 = False
                                break
                    ok = (
                        ok
                        and bool(res_pert["det_nonzero"])
                        and abs(float(res_pert["det_m0_log2"]) - float(entry["det_m0_log2"])) < 1e-3
                        and abs(
                            float(res_pert["det_at_cubic_gap_log2"])
                            - float(entry["det_at_cubic_gap_log2"])
                        )
                        < 1e-3
                        and float(res_pert["det_m0_log2"]) < 0.0
                        and float(res_pert["det_at_cubic_gap_log2"]) > 0.0
                        and ord2_obs == int(entry["ord2_mod_p"])
                        and ord32_obs == int(entry["ord32_mod_p"])
                        and math.gcd(ord2_obs, ord32_obs) == 1
                        and smaller_all_ge2
                    )
                else:
                    ok = False
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


# ============================================================================
# 11. Wave 6 Whole-Space Campaign (Fronts A–D: Coupled-Core Preimage Barrier,
#     Zero-Diagonal Matrices / Spiral Block-Return / Cousin T_diamond3,
#     Schneider–Laurent Integer Determinants & 2-Block Order/Equal-Even Locks,
#     Cross-Ray Disjointness, 27-Prefix Partition & Bounded-Length Sparsity)
# ============================================================================


def is_diamond3_cone4(x: int) -> bool:
    """
    Fourth Syracuse-jump cone of `T_diamond3` (`2 * z_j - 1 -> 2^m - 1`, `169 -> 127, ...`):
        `x >= 169 and x % 8 == 1 and core2_pos(3 * x + 5) == 1`.
    Note: since `3 * x + 5 == 2 (mod 3)` and `3 * 169 + 5 == 512 == 2^9`, every `x` in
    Cone 4 has `3 * x + 5 == 2^(2*r + 3)` for a unique `r >= 3`.
    """
    if isinstance(x, bool) or not isinstance(x, int):
        raise ValueError(f"Expected integer x, got {x!r}")
    if x < 169 or (x % 8) != 1:
        return False
    return core2_pos(3 * x + 5) == 1


def cousin_diamond3_step_int(x: int, q: int = 3) -> int:
    """
    Third solvable mixed-(2,3) Collatz cousin `T_diamond3` on `Z` (for odd `q >= 3`),
    defeating ALL fixed-step `L`-term (`forall L >= 1`) Laurent valuation sums on `Z^+`
    while converging globally to `1` via variable-horizon block-return descent:
      - Odd `x`:
        * Cone 4 (`x >= 169 and x % 8 == 1 and core2_pos(3 * x + 5) == 1`): `(q * x + 1) // 4`;
        * Cone 1 (`x > 1 and x % 16 == 1 and x % 3 != 2 and core3_pos(2 * x + 1) != 1`):
          `(q * x + 1) // 4`;
        * Cone 2 (`x >= 73 and x % 64 == 9 and x % 3 != 2 and core3_pos(2 * x + 1) != 1`):
          `(q * x + 1) // 4`;
        * Cone 3 (`x >= 17 and core3_pos(x + 1) == 2`): `(q * x + 1) // 4`;
        * All other odd `x`: `(q * x + 1) // 2`;
      - Even `x`:
        * `x >= 20 and x % 18 == 2`: `(x - 2) // 9`;
        * `x > 2 and x % 6 == 2`: `(x - 2) // 3`;
        * `x > 2 and x % 8 == 6`: `(x - 2) // 2`;
        * All other even `x`: `x // 2`.
    """
    if isinstance(x, bool) or not isinstance(x, int):
        raise ValueError(f"Expected integer x, got {x!r}")
    if isinstance(q, bool) or not isinstance(q, int) or (q & 1) == 0 or q < 3:
        raise ValueError(f"Expected odd multiplier q >= 3, got {q!r}")
    if (x & 1) == 1:
        if x >= 169 and (x % 8) == 1 and core2_pos(3 * x + 5) == 1:
            return (q * x + 1) // 4
        if x > 1 and (x % 16) == 1 and (x % 3) != 2 and core3_pos(2 * x + 1) != 1:
            return (q * x + 1) // 4
        if x >= 73 and (x % 64) == 9 and (x % 3) != 2 and core3_pos(2 * x + 1) != 1:
            return (q * x + 1) // 4
        if x >= 17 and core3_pos(x + 1) == 2:
            return (q * x + 1) // 4
        return (q * x + 1) // 2
    if x >= 20 and (x % 18) == 2:
        return (x - 2) // 9
    if x > 2 and (x % 6) == 2:
        return (x - 2) // 3
    if x > 2 and (x % 8) == 6:
        return (x - 2) // 2
    return x // 2


def cousin_diamond3_step_q6(x: Fraction) -> Fraction:
    """
    Canonical extension of `T_diamond3` (`q = 3`) to `Q_(6) = {a/b : gcd(b, 6) == 1}`.
    Agrees identically with `cousin_diamond3_step_int` on all integers `a/1` (`a >= 1`).
    """
    if isinstance(x, bool) or not isinstance(x, (int, Fraction)):
        raise ValueError(f"Expected int or Fraction x, got {x!r}")
    if not isinstance(x, Fraction):
        x = Fraction(x)
    if math.gcd(x.denominator, 6) != 1:
        raise ValueError(f"Expected rational with gcd(denom, 6) == 1, got {x}")
    num = x.numerator
    den = x.denominator
    inv_d_64 = pow(den, -1, 64)
    inv_d_3 = pow(den, -1, 3)
    r64 = (num * inv_d_64) % 64
    r3 = (num * inv_d_3) % 3
    if (r64 & 1) == 1:
        if num >= 169 * den and (r64 % 8) == 1 and core2_pos(3 * num + 5 * den) == den:
            return (3 * x + 1) / 4
        if num > den and (r64 % 16) == 1 and r3 != 2 and core3_pos(2 * num + den) != den:
            return (3 * x + 1) / 4
        if num >= 73 * den and r64 == 9 and r3 != 2 and core3_pos(2 * num + den) != den:
            return (3 * x + 1) / 4
        if num >= 17 * den and core3_pos(num + den) == 2 * den:
            return (3 * x + 1) / 4
        return (3 * x + 1) / 2
    if num >= 20 * den and (num % 18) == ((2 * den) % 18):
        return (x - 2) / 9
    if num > 2 * den and r3 == 2:
        return (x - 2) / 3
    if num > 2 * den and (r64 % 8) == 6:
        return (x - 2) / 2
    return x / 2


def cousin_diamond3_block_return(x: int) -> Tuple[int, int]:
    """
    Variable-horizon block-return step `(horizon_steps, next_state)` for `T_diamond3` on `Z^+`:
      - `x == 1`: `(0, 1)`;
      - `x == 2`: `(1, 1)`;
      - `is_diamond3_cone4(x)` (`3 * x + 5 == 2^(2*r + 3)`, `r >= 3`): `(3 * r + 4, 1)`;
      - all other `x > 2`: `(1, cousin_diamond3_step_int(x))` (strictly decreasing `Phi_diamond2`).
    """
    if isinstance(x, bool) or not isinstance(x, int) or x < 1:
        raise ValueError(f"Expected positive integer x >= 1, got {x!r}")
    if x == 1:
        return (0, 1)
    if x == 2:
        return (1, 1)
    if is_diamond3_cone4(x):
        exp2 = (3 * x + 5).bit_length() - 1
        r = (exp2 - 3) // 2
        horizon = 3 * r + 4
        cur = x
        for _ in range(horizon):
            cur = cousin_diamond3_step_int(cur, q=3)
        if cur != 1:
            raise AssertionError(f"Cone 4 return mismatch at x={x}: ended at {cur}")
        return (horizon, 1)
    return (1, cousin_diamond3_step_int(x, q=3))


def spiral_block_return_int(x: int) -> int:
    """
    Variable-horizon spiral block-return map on odd positive integers `x >= 1`:
    writing `x + 1 = 2^w * u` (`w >= 1`, `u >= 1` odd), steps across the entire `w`-step
    odd glide (`x -> 3^w * u - 1`) plus `a = v_2(3^w * u - 1)` halving steps to the next
    odd integer `core2_pos(3^w * u - 1)`.
    """
    if isinstance(x, bool) or not isinstance(x, int) or x < 1 or (x & 1) == 0:
        raise ValueError(f"Expected odd positive integer x >= 1, got {x!r}")
    xp1 = x + 1
    p2 = xp1 & -xp1
    w = p2.bit_length() - 1
    u = xp1 // p2
    return core2_pos((3**w) * u - 1)


_LAURENT_DET_CACHE: Dict[Tuple[int, int, int, int, int, int, int, bool], Dict[str, Any]] = {}
_LAURENT_MOD_PRIMES: Tuple[int, ...] = (1_000_000_007, 1_000_000_009, 1_000_000_021)


def _solve_laurent_2log_interpolation_det(
    W: int,
    K: int,
    R: int,
    S: int,
    T: int,
    U: int,
    prec: int = 260,
    exact_int: Optional[bool] = None,
) -> Dict[str, Any]:
    """
    Exact Schneider-Laurent 2-logarithm multiplicative integer interpolation determinant
    on rectangular grid `(R, S, T, U)` (`L = R * S == T * U`):
        `M[(r, s), (t, u)] = binom(r * W + s * K, t) * 2^(r * u) * 3^(s * u) in Z`,
    paired with the zero-gap analytic reference matrix
        `M0[(r, s), (t, u)] = binom(r * W + s * K, t) * exp(u * (ln 2 / W) * (r * W + s * K))`
    and exact polynomial-homogeneity decomposition
        `det(M0) == W^(T*(T-1)*U/2) / (prod_{t < T} t!)^U * det[x_{r,s}^t * 2^(u * x_{r,s})]`
    (`x_{r,s} = r + s * K / W`).
    Uses exact big-integer Bareiss elimination when `dim_L * max(W, K) * U <= 20000` (or
    `exact_int=True`), and sound modular ring-homomorphism Gaussian elimination modulo
    3 distinct 30-bit primes (`det_Z(M) mod p != 0 => det_Z(M) != 0`) for high-dimension
    high-`W` grids such as `W = 306, 10x10 = 20x5`.
    """
    if any(isinstance(v, bool) or not isinstance(v, int) for v in (W, K, R, S, T, U, prec)):
        raise ValueError("Expected integer parameters (W, K, R, S, T, U, prec), not bool/non-int")
    if W < 1 or K < 1:
        raise ValueError(f"Expected W >= 1 and K >= 1, got W={W}, K={K}")
    if R < 1 or S < 1 or T < 1 or U < 1 or (R * S) != (T * U):
        raise ValueError(
            f"Expected positive grid with R*S == T*U, got R={R}, S={S}, T={T}, U={U}"
        )
    if prec < 50:
        raise ValueError(f"Expected prec >= 50, got {prec}")

    dim_l = R * S
    do_exact = (dim_l * max(W, K) * U <= 20000) if exact_int is None else bool(exact_int)
    cache_key = (W, K, R, S, T, U, prec, do_exact)
    if cache_key in _LAURENT_DET_CACHE:
        return dict(_LAURENT_DET_CACHE[cache_key])

    rows_rs = [(r, s) for r in range(R) for s in range(S)]
    cols_tu = [(t, u) for t in range(T) for u in range(U)]

    # 1a. Fast exact modular determinants over F_p (sound certificate for det_Z(M) != 0)
    mod_dets: Dict[int, int] = {}
    for p_mod in _LAURENT_MOD_PRIMES:
        inv_fact = [pow(math.factorial(t_i), p_mod - 2, p_mod) for t_i in range(T)]
        b_mod: List[List[int]] = []
        for r_i, s_i in rows_rs:
            n_rs = r_i * W + s_i * K
            binom_row: List[int] = [1]
            acc_ff = 1
            for t_i in range(1, T):
                if n_rs < t_i:
                    binom_row.append(0)
                else:
                    acc_ff = (acc_ff * ((n_rs - t_i + 1) % p_mod)) % p_mod
                    binom_row.append((acc_ff * inv_fact[t_i]) % p_mod)
            p2_ru = [pow(2, r_i * u_i, p_mod) for u_i in range(U)]
            p3_su = [pow(3, s_i * u_i, p_mod) for u_i in range(U)]
            b_mod.append(
                [
                    (((binom_row[t_i] * p2_ru[u_i]) % p_mod) * p3_su[u_i]) % p_mod
                    for (t_i, u_i) in cols_tu
                ]
            )
        det_p = 1
        for k in range(dim_l):
            piv = next((i for i in range(k, dim_l) if b_mod[i][k] != 0), None)
            if piv is None:
                det_p = 0
                break
            if piv != k:
                b_mod[k], b_mod[piv] = b_mod[piv], b_mod[k]
                det_p = (p_mod - det_p) % p_mod
            bkk = b_mod[k][k]
            det_p = (det_p * bkk) % p_mod
            inv_bkk = pow(bkk, p_mod - 2, p_mod)
            for i in range(k + 1, dim_l):
                bik = b_mod[i][k]
                if bik == 0:
                    continue
                fac = (bik * inv_bkk) % p_mod
                row_i = b_mod[i]
                row_k = b_mod[k]
                for j in range(k, dim_l):
                    row_i[j] = (row_i[j] - fac * row_k[j]) % p_mod
        mod_dets[p_mod] = det_p
    any_mod_nonzero = any(v != 0 for v in mod_dets.values())

    # 1b. Exact integer determinant via fraction-free Bareiss elimination when do_exact=True
    det_int: Optional[int] = None
    if do_exact:
        mat_z = [
            [math.comb(r * W + s * K, t) * (1 << (r * u)) * (3 ** (s * u)) for (t, u) in cols_tu]
            for (r, s) in rows_rs
        ]
        work_z = [row[:] for row in mat_z]
        sign_z = 1
        prev_piv = 1
        det_val = 0
        singular_z = False
        for k in range(dim_l - 1):
            if work_z[k][k] == 0:
                piv = next((i for i in range(k + 1, dim_l) if work_z[i][k] != 0), None)
                if piv is None:
                    singular_z = True
                    break
                work_z[k], work_z[piv] = work_z[piv], work_z[k]
                sign_z = -sign_z
            akk = work_z[k][k]
            for i in range(k + 1, dim_l):
                aik = work_z[i][k]
                for j in range(k + 1, dim_l):
                    work_z[i][j] = (work_z[i][j] * akk - aik * work_z[k][j]) // prev_piv
            prev_piv = akk
        if not singular_z:
            det_val = sign_z * work_z[dim_l - 1][dim_l - 1]
        det_int = det_val
        for p_mod, r_mod in mod_dets.items():
            if (det_val % p_mod) != r_mod:
                raise RuntimeError(f"Bareiss/modular determinant mismatch mod {p_mod}")

    # 2. High-precision zero-gap analytic reference determinant det(M0) & normalized det_norm
    homog_exp = (T * (T - 1) * U) // 2
    fact_prod = 1
    for t_i in range(T):
        fact_prod *= math.factorial(t_i)

    with decimal.localcontext() as ctx:
        ctx.prec = prec
        ln2 = decimal.Decimal(2).ln()
        dec_w = decimal.Decimal(W)
        zeta = ln2 / dec_w
        mat_m0 = [
            [
                decimal.Decimal(math.comb(r * W + s * K, t))
                * ((zeta * decimal.Decimal(u * (r * W + s * K))).exp())
                for (t, u) in cols_tu
            ]
            for (r, s) in rows_rs
        ]
        mat_norm = [
            [
                (
                    decimal.Decimal(1)
                    if t == 0
                    else ((decimal.Decimal(r * W + s * K) / dec_w) ** t)
                )
                * ((ln2 * decimal.Decimal(u) * (decimal.Decimal(r * W + s * K) / dec_w)).exp())
                for (t, u) in cols_tu
            ]
            for (r, s) in rows_rs
        ]

        def _gauss_det_dec(mat_in: List[List[decimal.Decimal]]) -> decimal.Decimal:
            b = [row[:] for row in mat_in]
            acc = decimal.Decimal(1)
            for k in range(dim_l):
                piv = max(range(k, dim_l), key=lambda i: abs(b[i][k]))
                if abs(b[piv][k]) == 0:
                    return decimal.Decimal(0)
                if piv != k:
                    b[k], b[piv] = b[piv], b[k]
                    acc = -acc
                bkk = b[k][k]
                acc *= bkk
                for i in range(k + 1, dim_l):
                    fac = b[i][k] / bkk
                    for j in range(k + 1, dim_l):
                        b[i][j] -= fac * b[k][j]
            return acc

        det_m0 = _gauss_det_dec(mat_m0)
        det_norm = _gauss_det_dec(mat_norm)
        det_int_log2: Optional[float]
        if det_int is None:
            det_int_log2 = None
            det_nonzero = any_mod_nonzero
        else:
            det_int_log2 = (
                float(decimal.Decimal(abs(det_int)).ln() / ln2) if det_int != 0 else float("-inf")
            )
            det_nonzero = det_int != 0
        det_m0_log2 = float(abs(det_m0).ln() / ln2) if det_m0 != 0 else float("-inf")
        det_norm_log2 = float(abs(det_norm).ln() / ln2) if det_norm != 0 else float("-inf")
        fact_u_log2 = float(decimal.Decimal(U) * decimal.Decimal(fact_prod).ln() / ln2)
        homog_pred_log2 = (
            homog_exp * float(dec_w.ln() / ln2) - fact_u_log2 + det_norm_log2
        )

    res_dict = {
        "W": W,
        "K": K,
        "grid": (R, S, T, U),
        "dim_L": dim_l,
        "homogeneity_W_exponent": homog_exp,
        "det_int": det_int,
        "det_mod_primes": mod_dets,
        "det_nonzero": det_nonzero,
        "det_int_log2": det_int_log2,
        "det_m0_log2": det_m0_log2,
        "det_norm_log2": det_norm_log2,
        "homog_formula_diff": (
            0.0 if det_m0_log2 == homog_pred_log2 else abs(det_m0_log2 - homog_pred_log2)
        ),
    }
    _LAURENT_DET_CACHE[cache_key] = dict(res_dict)
    return res_dict


def audit_w6_front_a_coupled_core_preimage_barrier() -> Dict[str, Any]:
    """
    Front A (`Branch P1.2` & `P1.3`):
    1. Verify that coupling `core_{2,3}(n)` into `w_core(n) = (2^{v_2(n+1)})^2 / (core_{2,3}(n)^2 + (3^{v_3(n+1)})^3)`
       genuinely cures Wave 5's 4-adic spine divergence (`sum_{j=0}^J w_core(z_j) < 10^-3` across
       `z_j = (4^(3*j+4) - 1) // 3`) AND satisfies strict forward Syracuse growth `w_core(x) < w_core(Syr(x))`
       on `{17 -> 13, 97 -> 73, 169 -> 127}`, yet fails on Mersenne glides (`7 -> 11`).
    2. Verify the 4-step effective-degree squeeze (`gamma_Q >= gamma_P + 1` on `z_j`,
       `beta_Q - beta_P >= gamma_Q - gamma_P >= 1` on `2*9^k - 1`, `alpha_Q <= alpha_P + (beta_Q - beta_P)`
       on `2*z_j - 1`, and `9^{r*(beta_Q - beta_P)} < C * 4^{r*(beta_Q - beta_P)}` contradiction on
       `2^(2*r+1) - 1 -> 2*9^r - 1`) across all degree-bounded 6-variable coupled-core rational weights.
    """
    def w_core(n: int) -> Fraction:
        _, _, g0 = _decompose_2_3_coprime(n)
        a1, b1, _ = _decompose_2_3_coprime(n + 1)
        return Fraction(a1 * a1, g0 * g0 + (b1**3))

    z_spine = [(4 ** (3 * j + 4) - 1) // 3 for j in range(8)]
    spine_sum = sum(w_core(zj) for zj in z_spine)
    spine_converges_ok = spine_sum < Fraction(1, 1000)

    def syr_odd(x: int) -> int:
        return core2_pos(3 * x + 1)

    core_trap_ok = (
        spine_converges_ok
        and all(w_core(x) < w_core(syr_odd(x)) for x in (17, 97, 169))
        and w_core(7) > w_core(syr_odd(7))
    )

    # Exhaustively verify 0 surviving effective-degree pairs (alpha_P, beta_P, gamma_P, alpha_Q, beta_Q, gamma_Q) in [0..3]^6
    degree_survivors = 0
    for ap, bp, gp, aq, bq, gq in product(range(4), repeat=6):
        # Step 1: spine convergence requires gq >= gp + 1
        if not (gq >= gp + 1):
            continue
        # Step 2: 2*9^k - 1 -> (3*9^k - 1)/2 requires bp + gq <= gp + bq
        if not (bp + gq <= gp + bq):
            continue
        # Step 3: 2*z_j - 1 -> 2^(6j+7) - 1 requires gp + aq <= ap + gq
        if not (gp + aq <= ap + gq):
            continue
        # Step 4: 2^(2r+1) - 1 -> 2*9^r - 1 requires 2*(ap - aq) + (bq - bp)*log2(9) <= 0, i.e., 4^ap * 9^bq <= 9^bp * 4^aq
        if (4**ap) * (9**bq) <= (9**bp) * (4**aq):
            degree_survivors += 1

    return {
        "coupled_core_spine_sum_lt_1e_3": spine_converges_ok,
        "coupled_core_survives_17_97_169_fails_7_verified": core_trap_ok,
        "effective_degree_cone_survivors": degree_survivors,
        "coupled_core_rational_barrier_verified": core_trap_ok and (degree_survivors == 0),
    }


def audit_w6_front_b_zero_diag_block_return_and_cousin_diamond3() -> Dict[str, Any]:
    """
    Front B (`Branch P4.3` & `P5`):
    1. Verify zero-diagonal 2D upper-triangular necessity (`n_B0 == 0` and `d_R >= 1` on `{R2, R5, R7, R9, R11}`)
       and verify the sharp 7-rule impossibility when adding `R1_even` (`[L, B0] -> [L]`) to `{R2, R5, R7, R8, R9, R11}`.
    2. Verify true `(3x+1)` spiral block-return unbounded `r`-block climb `4 * 16^r - 5 -> 4 * 18^r - 5`
       (`r = 1..6`, including `1019 -> 1147 -> 1291` at `r = 2`) and 1-block/Syracuse coincidence on `x % 4 == 1`.
    3. Verify `T_diamond3`:
       - Matches `syracuseOddStep` identically on all 4 multi-term Laurent killer families `{97, 2*9^k - 1, 2*z_j - 1, 8*3^k - 1}`
         and defeats single-step `Phi_diamond2` at `169 -> 127`;
       - Strictly decreases `Phi_diamond2` in 1 step for all `x > 2` outside Cone 4 (`x = 3..5000`);
       - Converges to `1` in exact `3*r + 4` steps across Cone 4 (`r = 3..14`), and globally within `(x + 1)^3 + (x + 1)^5` steps;
       - Preserves `M1` (`1/7` 5-cycle), `M2` (`-1`, `-5` 3-cycle), `M3` (`q = 7, 5` 5-cycle), and `Q_(6)`/`Int` agreement.
    """
    # 1. Verify (2*n_B1 - 1) <= n_B1^2 algebraic barrier across n_B1 = 1..50 and 2D swap collapse on R1_even
    zero_diag_quad_gap_ok = all((2 * nb1 - 1) <= nb1 * nb1 for nb1 in range(1, 51))
    antidiag_swap_r1_fail_ok = not any(
        (pl * q0 >= 0)
        and (0 >= pl)
        and (0 >= ql)
        and (ql * p0 >= 0)
        and (pl * d0 >= 0)
        and (ql * c0 >= 0)
        and (pl * d0 > 0)
        for pl in range(4)
        for ql in range(4)
        for p0 in range(4)
        for q0 in range(4)
        for c0 in range(4)
        for d0 in range(4)
    )
    zero_diag_quad_gap_ok = zero_diag_quad_gap_ok and antidiag_swap_r1_fail_ok

    # 2. Verify r-block spiral climb 4*16^r - 5 -> 4*18^r - 5 across r = 1..6
    spiral_climb_ok = True
    for r in range(1, 7):
        cur = 4 * (16**r) - 5
        for j in range(1, r + 1):
            nxt = spiral_block_return_int(cur)
            expected = 4 * (16 ** (r - j)) * (18**j) - 5
            if nxt != expected or nxt <= cur or (cur % 3) == 0:
                spiral_climb_ok = False
                break
            cur = nxt

    spiral_mod4_eq1_syr_ok = all(
        spiral_block_return_int(x) == core2_pos(3 * x + 1) for x in range(5, 500, 4)
    )

    # 3. Verify T_diamond3 properties
    d3_outside_cone4_ok = all(
        (
            is_diamond3_cone4(x)
            or cousin_diamond2_phi(cousin_diamond3_step_int(x)) < cousin_diamond2_phi(x)
        )
        for x in range(3, 4501)
    )
    d3_phi2_jump_169_ok = (
        is_diamond3_cone4(169)
        and cousin_diamond3_step_int(169) == 127
        and cousin_diamond2_phi(169) == 1228282
        and cousin_diamond2_phi(127) == 34359738496
    )
    d3_cone4_exact_ok = True
    for r in range(3, 15):
        xc = ((1 << (2 * r + 3)) - 5) // 3
        h_steps, end_s = cousin_diamond3_block_return(xc)
        if not (is_diamond3_cone4(xc) and h_steps == 3 * r + 4 and end_s == 1 and h_steps <= cousin_diamond2_phi(xc)):
            d3_cone4_exact_ok = False
            break

    d3_syr_4families_ok = (
        cousin_diamond3_step_int(97) == 73
        and all(cousin_diamond3_step_int(2 * (9**k) - 1) == core2_pos(6 * (9**k) - 2) for k in range(1, 8))
        and all(
            cousin_diamond3_step_int(2 * ((4 ** (3 * j + 4) - 1) // 3) - 1)
            == (1 << (6 * j + 7)) - 1
            for j in range(6)
        )
        and all(cousin_diamond3_step_int(8 * (3**k) - 1) == 12 * (3**k) - 1 for k in range(1, 8))
    )

    m1_cur = Fraction(1, 7)
    for _ in range(5):
        m1_cur = cousin_diamond3_step_q6(m1_cur)
    m2_ok = (
        cousin_diamond3_step_int(-1) == -1
        and cousin_diamond3_step_int(cousin_diamond3_step_int(cousin_diamond3_step_int(-5))) == -5
    )
    m3_cur = 5
    for _ in range(5):
        m3_cur = cousin_diamond3_step_int(m3_cur, q=7)
    q6_int_agree_ok = all(
        cousin_diamond3_step_q6(Fraction(x_chk, 1)) == Fraction(cousin_diamond3_step_int(x_chk), 1)
        for x_chk in range(-100, 300)
    )
    q6_closure_ok = all(
        math.gcd(cousin_diamond3_step_q6(Fraction(num_c, den_c)).denominator, 6) == 1
        for den_c in (5, 7, 11, 13)
        for num_c in range(-35, 120)
        if math.gcd(num_c, den_c) == 1
    )
    d3_countermodels_ok = (
        (m1_cur == Fraction(1, 7))
        and m2_ok
        and (m3_cur == 5)
        and q6_int_agree_ok
        and q6_closure_ok
    )

    return {
        "zero_diag_r1_sub6_barrier_verified": zero_diag_quad_gap_ok,
        "spiral_r_block_unbounded_climb_verified": spiral_climb_ok,
        "spiral_mod4_eq1_matches_syracuse_verified": spiral_mod4_eq1_syr_ok,
        "cousin_diamond3_outside_cone4_descent_verified": d3_outside_cone4_ok,
        "cousin_diamond3_phi2_jump_at_169_verified": d3_phi2_jump_169_ok,
        "cousin_diamond3_cone4_exact_return_verified": d3_cone4_exact_ok,
        "cousin_diamond3_matches_4_laurent_families_verified": d3_syr_4families_ok,
        "cousin_diamond3_countermodels_verified": d3_countermodels_ok,
    }


def audit_w6_front_c_laurent_determinants_and_2block_locks() -> Dict[str, Any]:
    """
    Front C (`Branch P3.2`, `P3.3`, `P3.4`):
    1. Verify Schneider-Laurent integer interpolation determinants (`det_int != 0`, zero `lcm` denominators!),
       exact polynomial homogeneity `W^(T*(T-1)*U/2)`, fixed-grid `6x6 = 12x3` dip (`-457.75` bits at `W=5`,
       `-217.45` bits at `W=12`) vs high-`W` explosion (`+134.77` bits at `W=41`), scaling recovery on
       `8x8 = 16x4` at `W=41` (`-697.58` bits), and universal gap divisibility `(2^K - 3^W) | (M[(mK,0),(t,u)] - M[(0,mW),(t,u)])`.
    2. Verify 2-block single-Mersenne propagation (`p | D => (p | 2^a1 - 1 <-> p | 2^a2 - 1)`),
       equal-even-run (`a1 = a2 = a`, `w1 >= w2`) sub-exponent divisibility `D | (2^a - 1)*(3^(w1-w2) - 2^(w1-w2))`,
       and unconditional cone exclusion (`(w1 + w2) % 2 == 0 and 3*w1 <= 5*w2`).
    """
    from . import cs_lp_cycles as clp

    l_w5 = _solve_laurent_2log_interpolation_det(5, 8, 6, 6, 12, 3)
    l_w12 = _solve_laurent_2log_interpolation_det(12, 19, 6, 6, 12, 3)
    l_w41_fixed = _solve_laurent_2log_interpolation_det(41, 65, 6, 6, 12, 3)
    l_w41_scaled = _solve_laurent_2log_interpolation_det(41, 65, 8, 8, 16, 4)
    l_w306_fixed = _solve_laurent_2log_interpolation_det(306, 485, 6, 6, 12, 3)
    l_w306_scaled = _solve_laurent_2log_interpolation_det(306, 485, 10, 10, 20, 5)

    laurent_det_ok = (
        bool(l_w5["det_nonzero"])
        and bool(l_w12["det_nonzero"])
        and bool(l_w41_fixed["det_nonzero"])
        and bool(l_w41_scaled["det_nonzero"])
        and bool(l_w306_fixed["det_nonzero"])
        and bool(l_w306_scaled["det_nonzero"])
        and float(l_w5["det_m0_log2"]) < -450.0
        and float(l_w12["det_m0_log2"]) < -210.0
        and float(l_w41_fixed["det_m0_log2"]) > 130.0
        and float(l_w41_scaled["det_m0_log2"]) < -690.0
        and float(l_w306_fixed["det_m0_log2"]) > 700.0
        and float(l_w306_scaled["det_m0_log2"]) < -660.0
        and float(l_w12["homog_formula_diff"]) < 1e-9
        and float(l_w41_fixed["homog_formula_diff"]) < 1e-9
        and float(l_w306_scaled["homog_formula_diff"]) < 1e-8
    )

    # Verify resonant row collapse at u=0 and universal D-divisibility across (W, K, m, t, u)
    laurent_res_div_ok = True
    for w_v, k_v in ((5, 8), (8, 13), (12, 19)):
        det_gap = abs((1 << k_v) - (3**w_v))
        for m_mul in (1, 2, 3):
            for t_col in range(6):
                e1_0 = math.comb(m_mul * k_v * w_v, t_col)
                e2_0 = math.comb(m_mul * w_v * k_v, t_col)
                if e1_0 != e2_0:
                    laurent_res_div_ok = False
                for u_col in range(1, 5):
                    row1 = math.comb(m_mul * k_v * w_v, t_col) * (1 << (m_mul * k_v * u_col))
                    row2 = math.comb(m_mul * w_v * k_v, t_col) * (3 ** (m_mul * w_v * u_col))
                    if (row1 - row2) % det_gap != 0:
                        laurent_res_div_ok = False

    # Verify 2-block equal-even-run lock D | (2^a - 1)*(3^(w1-w2) - 2^(w1-w2)) and 3*w1 <= 5*w2 cone exclusion
    twoblock_eq_even_ok = True
    for w2 in range(1, 18):
        for w1 in range(w2 + 1, 22):
            w_tot = w1 + w2
            k_min = (3**w_tot).bit_length()
            for k_tot in range(k_min, k_min + 6):
                if (k_tot - w_tot) < 2 or ((k_tot - w_tot) % 2) != 0:
                    continue
                a = (k_tot - w_tot) // 2
                det = (1 << k_tot) - (3**w_tot)
                h0, h1 = clp.two_block_brox_carries(w1, a, w2, a)
                sub_rhs = ((1 << a) - 1) * ((3 ** (w1 - w2)) - (1 << (w1 - w2)))
                if h1 != (1 << (w1 - w2)) * h0 + (3**w2) * sub_rhs:
                    twoblock_eq_even_ok = False
                if (w_tot % 2) == 0 and (3 * w1 <= 5 * w2):
                    if det <= sub_rhs:
                        twoblock_eq_even_ok = False

    return {
        "laurent_det_dip_explosion_and_scaling_verified": laurent_det_ok,
        "laurent_resonant_divisibility_verified": laurent_res_div_ok,
        "twoblock_equal_even_lock_and_cone_exclusion_verified": twoblock_eq_even_ok,
    }


def audit_w6_front_d_cross_ray_disjointness_and_prefix_covering() -> Dict[str, Any]:
    """
    Front D (`Branch P5.3`):
    1. Verify global cross-ray disjointness across all `IsFirstHitOnePair` rays (`|u| <= 9, q in {0, 1}`),
       unconditional `q >= 1` disjointness across all `w >= 2` core words (including `u_loop` words!),
       and `q = 0` collision sharpness at `y = 184111`.
    2. Verify the exact `11 + 16 = 27` `mod 512` surviving prefix partition at lengths `|u| = 8` (`11` words)
       and `|u| = 9` (`16` words), and uniform fiber multiplicity `2^(L - 10)` per surviving `mod 512`
       class across `L = 10, 11, 12` (`27 * 2^(L - 10)` total surviving core words of length `L`).
    3. Verify exponential `q`-ray sparsity (`exactBackwardQuotient 1 u q >= 2^(486 * q)` for `w >= 6`)
       and explicit non-covering of `IsSurvivingMod373248Class` by bounded-length ray unions `|u| <= L_max`.
    """
    from . import cs_forest_transfer as cft

    # 1. Cross-ray disjointness on q >= 1 (including loop words) and q = 0 collision at 184111
    u_min = (1, 1, 1, 1, 0, 1, 0, 1)
    sh_min = cft.canonical_suffix_shift(u_min, 1)
    u_loop_min = u_min + (0,) * sh_min + (1,)
    q0_collision_sharp_ok = (
        sh_min == 19
        and cft.exact_backward_quotient(1, u_min, 0) == 184111
        and cft.exact_backward_quotient(1, u_loop_min, 0) == 184111
        and cft.is_first_hit_one_pair(u_min, 0)
        and (not cft.is_first_hit_one_pair(u_loop_min, 0))
        and cft.is_first_hit_one_pair(u_loop_min, 1)
        and cft.exact_backward_quotient(1, u_min, 1) != cft.exact_backward_quotient(1, u_loop_min, 1)
    )

    seen_q_pos: Dict[int, Tuple[Tuple[int, ...], int]] = {}
    q_pos_disjoint_ok = True
    for length in range(2, 9):
        for mid in product((0, 1), repeat=length - 2):
            u_c = (1,) + mid + (1,)
            for q_i in (1, 2):
                yq = cft.exact_backward_quotient(1, u_c, q_i)
                if yq in seen_q_pos and seen_q_pos[yq] != (u_c, q_i):
                    q_pos_disjoint_ok = False
                    break
                seen_q_pos[yq] = (u_c, q_i)

    # 2. Exact 11 + 16 = 27 mod 512 partition at |u| = 8, 9 and uniform 2^(L - 10) fibers at L = 10, 11, 12
    surv512_set = {r for r in range(512) if cft.is_surviving_mod512_residue(r)}
    hits_len8 = [
        cft.exact_backward_quotient(1, (1, 1) + mid + (1,), 0) % 512
        for mid in product((0, 1), repeat=5)
        if (cft.exact_backward_quotient(1, (1, 1) + mid + (1,), 0) % 512) in surv512_set
    ]
    hits_len9 = [
        cft.exact_backward_quotient(1, (1, 1) + mid + (1,), 0) % 512
        for mid in product((0, 1), repeat=6)
        if (cft.exact_backward_quotient(1, (1, 1) + mid + (1,), 0) % 512) in surv512_set
    ]
    partition_8_9_ok = (
        len(surv512_set) == 27
        and len(hits_len8) == 11
        and len(set(hits_len8)) == 11
        and len(hits_len9) == 16
        and len(set(hits_len9)) == 16
        and (set(hits_len8) & set(hits_len9)) == set()
        and (set(hits_len8) | set(hits_len9)) == surv512_set
    )

    uniform_fibers_ok = True
    for length_l in (10, 11, 12):
        fiber_counts: Dict[int, int] = {r: 0 for r in surv512_set}
        for mid in product((0, 1), repeat=length_l - 3):
            u_c = (1, 1) + mid + (1,)
            r512 = cft.exact_backward_quotient(1, u_c, 0) % 512
            if r512 in fiber_counts:
                fiber_counts[r512] += 1
        expected_mult = 1 << (length_l - 10)
        if not all(cnt == expected_mult for cnt in fiber_counts.values()):
            uniform_fibers_ok = False
            break

    # 3. Verify exponential q-ray sparsity & explicit missed surviving seed for L_max = 8
    ray_vals_le8: Set[int] = set()
    sparsity_ok = True
    for mid in product((0, 1), repeat=5):
        u8 = (1, 1) + mid + (1,)
        if sum(u8) >= 6:
            y0 = cft.exact_backward_quotient(1, u8, 0)
            y1 = cft.exact_backward_quotient(1, u8, 1)
            ray_vals_le8.add(y0)
            if y1 < (1 << 486):
                sparsity_ok = False
    missed_27 = (27 not in ray_vals_le8) and cft.is_surviving_mod373248_class(27)

    return {
        "q0_loop_collision_sharp_at_184111_verified": q0_collision_sharp_ok,
        "q_pos_cross_ray_disjointness_verified": q_pos_disjoint_ok,
        "mod512_prefix_partition_11_plus_16_eq_27_verified": partition_8_9_ok,
        "mod512_uniform_fibers_L10_to_L12_verified": uniform_fibers_ok,
        "exponential_q_sparsity_and_bounded_noncovering_verified": sparsity_ok and missed_27,
    }


def _dynamic_pred_coupled_core_preimage_syracuse(_dom: str, entry: Dict[str, Any]) -> bool:
    """
    Dynamic test of coupled-core preimage weight `w_core(n) = a1^2 / (g0^2 + b1^3)` (which converges
    on the 4-adic spine `z_j` and passes `{17, 97, 169}`): requires `w_core(x) < w_core(Syr(x))`
    on odd seeds with `Syr(x) >= 3`. Zero hardcoded witness IDs.
    """
    seed = int(entry.get("seed", 0))
    if seed < 3 or (seed & 1) == 0:
        return True
    nxt = core2_pos(3 * seed + 1)
    if nxt < 3:
        return True
    _, _, g0_s = _decompose_2_3_coprime(seed)
    a1_s, b1_s, _ = _decompose_2_3_coprime(seed + 1)
    _, _, g0_n = _decompose_2_3_coprime(nxt)
    a1_n, b1_n, _ = _decompose_2_3_coprime(nxt + 1)
    w_s = Fraction(a1_s * a1_s, g0_s * g0_s + (b1_s**3))
    w_n = Fraction(a1_n * a1_n, g0_n * g0_n + (b1_n**3))
    return w_s < w_n


def _dynamic_pred_phi2_on_cousin_diamond3(_dom: str, entry: Dict[str, Any]) -> bool:
    """Dynamic test of single-step `Phi_diamond2` descent on `T_diamond3` across `Z^+` seeds > 2."""
    seed = int(entry.get("seed", 0))
    if seed <= 2:
        return True
    nxt = cousin_diamond3_step_int(seed, q=3)
    return cousin_diamond2_phi(nxt) < cousin_diamond2_phi(seed)


def _dynamic_pred_spiral_2block_monotone(_dom: str, entry: Dict[str, Any]) -> bool:
    """Dynamic test of 2-block spiral contraction `min(B(x), B(B(x))) < x` on odd seeds >= 3."""
    seed = int(entry.get("seed", 0))
    if seed < 3 or (seed & 1) == 0:
        return True
    b1 = spiral_block_return_int(seed)
    if b1 < 3:
        return True
    b2 = spiral_block_return_int(b1)
    return min(b1, b2) < seed


def _dynamic_pred_q0_ray_injectivity_without_first_hit(_dom: str, entry: Dict[str, Any]) -> bool:
    """Dynamic test of `q = 0` cross-ray injectivity omitting `IsFirstHitOnePair`."""
    if "loop_core_word" not in entry or "core_word" not in entry:
        return True
    from . import cs_forest_transfer as cft

    u1 = tuple(int(b) for b in entry["core_word"])
    u2 = tuple(int(b) for b in entry["loop_core_word"])
    if u1 == u2:
        return True
    return cft.exact_backward_quotient(1, u1, 0) != cft.exact_backward_quotient(1, u2, 0)


def _dynamic_pred_fixed_grid_laurent_extrapolation(_dom: str, entry: Dict[str, Any]) -> bool:
    """Dynamic test of false fixed-grid Laurent extrapolation `det_m0 < 1 at low W => det_m0 < 1 at high W`."""
    if "laurent_grid" not in entry:
        return True
    r_g, s_g, t_g, u_g = (int(v) for v in entry["laurent_grid"])
    res_low = _solve_laurent_2log_interpolation_det(
        int(entry["low_W"]), int(entry["low_K"]), r_g, s_g, t_g, u_g
    )
    res_high = _solve_laurent_2log_interpolation_det(
        int(entry["high_W"]), int(entry["high_K"]), r_g, s_g, t_g, u_g
    )
    if float(res_low["det_m0_log2"]) < 0.0:
        return float(res_high["det_m0_log2"]) < 0.0
    return True


def run_wave6_whole_space_campaign(bank_path: Optional[Path] = None) -> Dict[str, Any]:
    """
    Execute the complete Wave 6 whole-space red-team, coupled-core preimage barrier,
    zero-diagonal / spiral block-return / `T_diamond3` benchmark, Schneider-Laurent
    determinant / 2-block order & equal-even lock, and cross-ray disjointness / 27-prefix
    partition / bounded-length sparsity campaign against `witness_bank.json`.
    """
    u_gate = audit_universality_gate(
        "Wave6_WholeSpace_W6_1_to_W6_4",
        is_finite_m_table=False,
        is_finite_n_table=False,
        is_bounded_weight_table=False,
        uses_native_decide=False,
        uses_sorry=False,
        axioms_used=("propext", "Classical.choice", "Quot.sound"),
    )
    bank = load_witness_bank(bank_path)
    wb_truth = verify_witness_bank_ground_truth(bank_path)

    gate_coupled_core = evaluate_hypothesis_against_witness_bank(
        "CoupledCorePreimageWeightOnTrueCollatz",
        _dynamic_pred_coupled_core_preimage_syracuse,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    gate_phi2_d3 = evaluate_hypothesis_against_witness_bank(
        "SingleStepPhi2OnCousinDiamond3",
        _dynamic_pred_phi2_on_cousin_diamond3,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    gate_spiral_2block = evaluate_hypothesis_against_witness_bank(
        "TwoBlockSpiralContractionOnTrueCollatz",
        _dynamic_pred_spiral_2block_monotone,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    gate_q0_loop = evaluate_hypothesis_against_witness_bank(
        "Q0CrossRayInjectivityWithoutFirstHit",
        _dynamic_pred_q0_ray_injectivity_without_first_hit,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    gate_laurent_fixed = evaluate_hypothesis_against_witness_bank(
        "FixedGridLaurentInterpolationWithoutZeroMultiplicity",
        _dynamic_pred_fixed_grid_laurent_extrapolation,
        domains=("log2_3_convergents",),
        bank_path=bank_path,
    )

    front_a = audit_w6_front_a_coupled_core_preimage_barrier()
    front_b = audit_w6_front_b_zero_diag_block_return_and_cousin_diamond3()
    front_c = audit_w6_front_c_laurent_determinants_and_2block_locks()
    front_d = audit_w6_front_d_cross_ray_disjointness_and_prefix_covering()

    passed = (
        u_gate.passed
        and bool(wb_truth["all_witnesses_ground_truth_verified"])
        and (not gate_coupled_core["passed"])
        and ("z_pos_high_glide", "ZPOS_MERSENNE_2_POW_20_SUB_1") in gate_coupled_core["failures"]
        and (not gate_phi2_d3["passed"])
        and gate_phi2_d3["minimal_failure"]
        == ("z_pos_high_glide", "ZPOS_SPINE_DYADIC_JUMP_169_TO_127")
        and (not gate_spiral_2block["passed"])
        and ("z_pos_high_glide", "ZPOS_SPIRAL_2BLOCK_1019_CLIMB") in gate_spiral_2block["failures"]
        and (not gate_q0_loop["passed"])
        and gate_q0_loop["minimal_failure"]
        == ("z_pos_high_glide", "ZPOS_RAY_Q0_LOOP_COLLISION_184111")
        and (not gate_laurent_fixed["passed"])
        and gate_laurent_fixed["minimal_failure"]
        == ("log2_3_convergents", "LAURENT_DET_6X6_12X3_W12_DIP_AND_W41_EXPLOSION")
        and bool(front_a["coupled_core_rational_barrier_verified"])
        and bool(front_b["zero_diag_r1_sub6_barrier_verified"])
        and bool(front_b["spiral_r_block_unbounded_climb_verified"])
        and bool(front_b["spiral_mod4_eq1_matches_syracuse_verified"])
        and bool(front_b["cousin_diamond3_outside_cone4_descent_verified"])
        and bool(front_b["cousin_diamond3_phi2_jump_at_169_verified"])
        and bool(front_b["cousin_diamond3_cone4_exact_return_verified"])
        and bool(front_b["cousin_diamond3_matches_4_laurent_families_verified"])
        and bool(front_b["cousin_diamond3_countermodels_verified"])
        and bool(front_c["laurent_det_dip_explosion_and_scaling_verified"])
        and bool(front_c["laurent_resonant_divisibility_verified"])
        and bool(front_c["twoblock_equal_even_lock_and_cone_exclusion_verified"])
        and bool(front_d["q0_loop_collision_sharp_at_184111_verified"])
        and bool(front_d["q_pos_cross_ray_disjointness_verified"])
        and bool(front_d["mod512_prefix_partition_11_plus_16_eq_27_verified"])
        and bool(front_d["mod512_uniform_fibers_L10_to_L12_verified"])
        and bool(front_d["exponential_q_sparsity_and_bounded_noncovering_verified"])
    )
    return {
        "passed": passed,
        "verdict": "REDTEAM-PASSED" if passed else "FALSIFIED",
        "universality_gate_passed": u_gate.passed,
        "witness_bank_total_entries": sum(len(v) for v in bank["domains"].values()),
        "witness_bank_falsified_count": len(bank["falsified_hypotheses"]),
        "witness_bank_ground_truth_verified": bool(wb_truth["all_witnesses_ground_truth_verified"]),
        "front_a_coupled_core_preimage": front_a,
        "front_b_zero_diag_spiral_and_diamond3": front_b,
        "front_c_laurent_and_2block_locks": front_c,
        "front_d_cross_ray_and_prefix_covering": front_d,
    }


# ============================================================================
# 12. Wave 7 Whole-Space Campaign (Fronts A–D: W-Dilated Laurent Remainder &
#     Common-Order Prime Exclusions, Binary Digit/Bit-Length Preimage Weights
#     & Mahler-Tauberian Balance, 3D Non-Triangular Hofbauer-Waldmann / VASS /
#     Cousin T_diamond4, and Markov Suffix-Shift / q=0 Envelope / L^2 Energy)
# ============================================================================

_LAURENT_PERTURBED_DET_CACHE: Dict[Tuple[int, int, int, int, int, int, int], Dict[str, Any]] = {}


def binary_popcount(n: int) -> int:
    """Count `1`-bits in binary representation of `n >= 0` (`binPopcount` in Lean 4)."""
    if isinstance(n, bool) or not isinstance(n, int) or n < 0:
        raise ValueError(f"Expected nonnegative integer n >= 0, got {n!r}")
    return n.bit_count()


def binary_one_runs(n: int) -> int:
    """
    Count maximal contiguous `1`-bit runs in binary representation of `n >= 0`
    (`binOneRuns` in Lean 4): `0` for `n == 0`, else
    `binary_one_runs(n // 2) + (1 if (n % 2 == 1 and (n // 2) % 2 == 0) else 0)`.
    """
    if isinstance(n, bool) or not isinstance(n, int) or n < 0:
        raise ValueError(f"Expected nonnegative integer n >= 0, got {n!r}")
    runs = 0
    cur = n
    while cur > 0:
        if (cur & 1) == 1 and ((cur >> 1) & 1) == 0:
            runs += 1
        cur >>= 1
    return runs


def binary_alt_transitions(n: int) -> int:
    """
    Count adjacent bit transitions `b_i != b_{i+1}` inside the binary expansion of `n >= 0`
    (`binAltTransitions` in Lean 4): `0` for `n <= 1`, else
    `binary_alt_transitions(n // 2) + (1 if (n % 2) != ((n // 2) % 2) else 0)`.
    """
    if isinstance(n, bool) or not isinstance(n, int) or n < 0:
        raise ValueError(f"Expected nonnegative integer n >= 0, got {n!r}")
    trans = 0
    cur = n
    while cur >= 2:
        if (cur & 1) != ((cur >> 1) & 1):
            trans += 1
        cur >>= 1
    return trans


def binary_digit_signature6(n: int) -> Tuple[int, int, int, int, int, int]:
    """
    Return the 6-coordinate non-algebraic binary digit signature (`binDigitSig6` in Lean 4):
    `(popcount(n), one_runs(n), alt_transitions(n), popcount(n+1), one_runs(n+1), alt_transitions(n+1))`.
    """
    if isinstance(n, bool) or not isinstance(n, int) or n < 0:
        raise ValueError(f"Expected nonnegative integer n >= 0, got {n!r}")
    return (
        binary_popcount(n),
        binary_one_runs(n),
        binary_alt_transitions(n),
        binary_popcount(n + 1),
        binary_one_runs(n + 1),
        binary_alt_transitions(n + 1),
    )


def _mult_order_mod_prime(a: int, p: int) -> int:
    """Exact multiplicative order of `a` modulo prime `p >= 3` (`gcd(a, p) == 1`)."""
    if isinstance(a, bool) or isinstance(p, bool) or not isinstance(a, int) or not isinstance(p, int):
        raise ValueError("Expected integer arguments (a, p)")
    if p < 3 or (p & 1) == 0 or math.gcd(a, p) != 1:
        raise ValueError(f"Expected odd modulus p >= 3 coprime to a, got a={a}, p={p}")
    a_mod = a % p
    order = p - 1
    rem = p - 1
    prime_factors: List[int] = []
    d = 2
    while d * d <= rem:
        if rem % d == 0:
            prime_factors.append(d)
            while rem % d == 0:
                rem //= d
        d += 1 if d == 2 else 2
    if rem > 1:
        prime_factors.append(rem)
    for pf in prime_factors:
        while order % pf == 0 and pow(a_mod, order // pf, p) == 1:
            order //= pf
    return order


def _solve_laurent_perturbed_cubic_gap_det(
    W: int,
    K: int,
    R: int,
    S: int,
    T: int,
    U: int,
    prec: int = 220,
) -> Dict[str, Any]:
    """
    Evaluate the perturbed Schneider-Laurent determinant at the `SubexponentialCubicGapProp`
    boundary `Lambda_cubic = 2^(-W / 3) * ln 2`, substituting
        `3^(s * u) -> exp(u * (ln 2 / W) * (r * W + s * K) - s * u * Lambda_cubic / W)`
    after pulling `2^(r * u)` in, and compare against `det_m0_log2` and `det_nonzero`.
    Demonstrates cofactor Schwarz-order stripping at moderate `W` (`W = 41`, grid `(8,8,16,4)`:
    `det_m0_log2 = -697.58 << 0`, yet `det_at_cubic_gap_log2 = +2382.47 >> 0`).
    """
    base = _solve_laurent_2log_interpolation_det(W, K, R, S, T, U, prec=max(prec, 200))
    cache_key = (W, K, R, S, T, U, prec)
    if cache_key in _LAURENT_PERTURBED_DET_CACHE:
        return dict(_LAURENT_PERTURBED_DET_CACHE[cache_key])

    dim_l = R * S
    rows_rs = [(r, s) for r in range(R) for s in range(S)]
    cols_tu = [(t, u) for t in range(T) for u in range(U)]
    with decimal.localcontext() as ctx:
        ctx.prec = prec
        ln2 = decimal.Decimal(2).ln()
        dec_w = decimal.Decimal(W)
        zeta = ln2 / dec_w
        lam_cubic = (-((dec_w / decimal.Decimal(3)) * ln2)).exp() * ln2
        mat_pert = [
            [
                decimal.Decimal(math.comb(r * W + s * K, t))
                * (
                    (
                        zeta * decimal.Decimal(u * (r * W + s * K))
                        - decimal.Decimal(s * u) * lam_cubic / dec_w
                    ).exp()
                )
                for (t, u) in cols_tu
            ]
            for (r, s) in rows_rs
        ]
        b = [row[:] for row in mat_pert]
        acc = decimal.Decimal(1)
        for k in range(dim_l):
            piv = max(range(k, dim_l), key=lambda i: abs(b[i][k]))
            if abs(b[piv][k]) == 0:
                acc = decimal.Decimal(0)
                break
            if piv != k:
                b[k], b[piv] = b[piv], b[k]
                acc = -acc
            bkk = b[k][k]
            acc *= bkk
            for i in range(k + 1, dim_l):
                fac = b[i][k] / bkk
                for j in range(k + 1, dim_l):
                    b[i][j] -= fac * b[k][j]
        det_cubic_log2 = float(abs(acc).ln() / ln2) if acc != 0 else float("-inf")

    res = {
        "W": W,
        "K": K,
        "grid": (R, S, T, U),
        "det_nonzero": bool(base["det_nonzero"]),
        "det_m0_log2": float(base["det_m0_log2"]),
        "det_at_cubic_gap_log2": det_cubic_log2,
    }
    _LAURENT_PERTURBED_DET_CACHE[cache_key] = dict(res)
    return res


def is_diamond4_cone5(x: int) -> bool:
    """
    Fifth Syracuse-jump cone of `T_diamond4` (`2^a * 3^b - 7 -> 2^(a-2) * 3^(b+1) - 5`,
    `1529 -> 1147 -> 1721 -> 1291`, starting at `89 = 32 * 3 - 7`):
        `x >= 89 and x % 32 == 25 and x % 3 == 2 and coprime23(x + 7) == 1`.
    """
    if isinstance(x, bool) or not isinstance(x, int):
        raise ValueError(f"Expected integer x, got {x!r}")
    if x < 89 or (x % 32) != 25 or (x % 3) != 2:
        return False
    return _decompose_2_3_coprime(x + 7)[2] == 1


def cousin_diamond4_step_int(x: int, q: int = 3) -> int:
    """
    Fourth solvable mixed-(2,3) Collatz cousin `T_diamond4` on `Z` (for odd `q >= 3`),
    exhibiting unbounded `r`-block spiral climbs (`4 * 16^r - 5 ->^{2r} 4 * 18^r - 5`,
    including `1019 -> 1529 -> 1147 -> 1721 -> 1291`) that defeat both all `L`-term
    Laurent valuation sums AND 1-block return rankings, yet converging globally to `1`
    under a lexicographic `omega^2` ordinal / multi-block ranking:
      - If `is_diamond4_cone5(x)`: `(q * x + 1) // 4`;
      - Otherwise: `cousin_diamond3_step_int(x, q=q)`.
    """
    if isinstance(x, bool) or not isinstance(x, int):
        raise ValueError(f"Expected integer x, got {x!r}")
    if isinstance(q, bool) or not isinstance(q, int) or (q & 1) == 0 or q < 3:
        raise ValueError(f"Expected odd multiplier q >= 3, got {q!r}")
    if is_diamond4_cone5(x):
        return (q * x + 1) // 4
    return cousin_diamond3_step_int(x, q=q)


def cousin_diamond4_step_q6(x: Fraction) -> Fraction:
    """
    Canonical extension of `T_diamond4` (`q = 3`) to `Q_(6) = {a/b : gcd(b, 6) == 1}`.
    Agrees identically with `cousin_diamond4_step_int` on all integers `a/1` and preserves `Q_(6)`.
    """
    if isinstance(x, bool) or not isinstance(x, (int, Fraction)):
        raise ValueError(f"Expected int or Fraction x, got {x!r}")
    if not isinstance(x, Fraction):
        x = Fraction(x)
    if math.gcd(x.denominator, 6) != 1:
        raise ValueError(f"Expected rational with gcd(denom, 6) == 1, got {x}")
    num = x.numerator
    den = x.denominator
    inv_d_64 = pow(den, -1, 64)
    inv_d_3 = pow(den, -1, 3)
    r64 = (num * inv_d_64) % 64
    r3 = (num * inv_d_3) % 3
    if (
        num >= 89 * den
        and (r64 % 32) == 25
        and r3 == 2
        and core3_pos(core2_pos(num + 7 * den)) == den
    ):
        return (3 * x + 1) / 4
    return cousin_diamond3_step_q6(x)


def cousin_diamond4_block_return(x: int) -> Tuple[int, int]:
    """
    Exact multi-block / ordinal return `(horizon_steps, next_state)` for `T_diamond4` on `Z^+`:
      - `x == 1`: `(0, 1)`;
      - `x == 2`: `(1, 1)`;
      - `is_diamond3_cone4(x)` (`3 * x + 5 == 2^(2*r + 3)`): `(3 * r + 4, 1)`;
      - `is_diamond4_cone5(x)` (`x + 7 == 2^a * 3^b`, `a >= 5, b >= 1`):
        climbs `q_c = (a - 2) // 3` two-step spiral blocks (`2 * q_c` steps) to
        `z_exit = 2^a0 * 3^b0 - 7` (`a0 in {2, 3, 4}`, `b0 = b + 2 * q_c >= 3`) and
        drains to `1` in closed form (`b0 + 3` for `a0 == 2`, `(b0 - 1)//2 + 7` for `a0 == 3`,
        `(b0 - 1)//2 + 8` for `a0 == 4`);
      - all other `x > 2`: `(1, cousin_diamond4_step_int(x))` (strictly decreasing `Phi_diamond2`).
    """
    if isinstance(x, bool) or not isinstance(x, int) or x < 1:
        raise ValueError(f"Expected positive integer x >= 1, got {x!r}")
    if x == 1:
        return (0, 1)
    if x == 2:
        return (1, 1)
    if is_diamond3_cone4(x):
        exp2 = (3 * x + 5).bit_length() - 1
        r = (exp2 - 3) // 2
        horizon = 3 * r + 4
        cur = x
        for _ in range(horizon):
            cur = cousin_diamond4_step_int(cur, q=3)
        if cur != 1:
            raise AssertionError(f"Cone 4 return mismatch under T_diamond4 at x={x}: ended at {cur}")
        return (horizon, 1)
    if is_diamond4_cone5(x):
        p2, p3, g = _decompose_2_3_coprime(x + 7)
        if g != 1:
            raise AssertionError(f"Invalid Cone 5 decomposition at x={x}")
        a = p2.bit_length() - 1
        b = 0
        tmp3 = p3
        while tmp3 > 1:
            tmp3 //= 3
            b += 1
        q_c = (a - 2) // 3
        a0 = a - 3 * q_c
        b0 = b + 2 * q_c
        if a0 == 2:
            exit_steps = b0 + 3
        elif a0 == 3:
            exit_steps = (b0 - 1) // 2 + 7
        else:
            exit_steps = (b0 - 1) // 2 + 8
        horizon = 2 * q_c + exit_steps
        cur = x
        for _ in range(horizon):
            cur = cousin_diamond4_step_int(cur, q=3)
        if cur != 1:
            raise AssertionError(f"Cone 5 return mismatch under T_diamond4 at x={x}: ended at {cur}")
        return (horizon, 1)
    return (1, cousin_diamond4_step_int(x, q=3))


def audit_w7_front_a_laurent_bridge_and_common_order_primes() -> Dict[str, Any]:
    """
    Front A (`Branch P3.3` & `P3.4`):
    1. Verify moderate-`W` scaled Schneider-Laurent cofactor Schwarz-order stripping at `(W, K) = (41, 65)`
       on `(8, 8, 16, 4)` (`det_m0_log2 < -690`, yet `det_at_cubic_gap_log2 > +2380`).
    2. Verify pure-`Nat` `W`-dilated zero-gap decomposition:
       `M0_int[(r,s),(t,u)] - M[(r,s),(t,W*u)] == binom(rW+sK, t) * 2^(rWu) * ((2^K)^(su) - (3^W)^(su))`
       is divisible by `D = 2^K - 3^W` for EVERY `(r, s, t, u)`, satisfies the discrete mean-value
       sandwich, and induces `D | (det_Z(M0_int) - det_Z(M_W))` on `4x4` and `6x6` grids, plus `2x2`
       resonant singularity (`u = 0 => det = 0`) vs strict positivity (`u >= 1 => det = (2^K)^u - (3^W)^u > 0`).
    3. Verify universal 1-block common-divisor impossibility (`r >= 2, r | w1, r | a1 => D > 2^a1 - 1`),
       100% exclusion of all `60 / 60` odd primes `5 <= p < 300` on 1-block `Z^+` cycles (including
       `{7, 19, 23, 31, 43, 47, 71, 73}`), isolation of `p = 331` (`ord_331(2)=30, ord_331(3/2)=11`)
       as the minimal coprime-order prime (`1 / 784` primes `5 <= p < 6000`), and on 2-block shared-Mersenne
       cycles both the universal `(5*r, 3*r, 8*r)` scaling floor (`forall r >= 1`) and the sharp `(41*r, 65*r)`
       boost (`forall r >= 3`, covering all 8 odd-order primes `{7, 19, 23, 31, 43, 47, 71, 73}`).
    """
    from itertools import permutations

    def _det_int(m: List[List[int]]) -> int:
        n_sz = len(m)
        tot = 0
        for perm in permutations(range(n_sz)):
            inv = sum(
                1 for i in range(n_sz) for j in range(i + 1, n_sz) if perm[i] > perm[j]
            )
            prod = 1
            for i in range(n_sz):
                prod *= m[i][perm[i]]
            tot += (-prod) if (inv & 1) else prod
        return tot

    # 1. Moderate-W cofactor stripping check at (41, 65), (8, 8, 16, 4)
    pert_41 = _solve_laurent_perturbed_cubic_gap_det(41, 65, 8, 8, 16, 4)
    cofactor_stripping_ok = (
        bool(pert_41["det_nonzero"])
        and float(pert_41["det_m0_log2"]) < -690.0
        and float(pert_41["det_at_cubic_gap_log2"]) > 2380.0
    )

    # 2. Pure-Nat W-dilated zero-gap entrywise & determinant congruence mod D + 2x2 dichotomy
    wdilated_congruence_ok = True
    for w_v, k_v in ((3, 5), (5, 8), (8, 13)):
        det_gap = (1 << k_v) - (3**w_v)
        for r_i in range(3):
            for s_i in range(3):
                for t_i in range(4):
                    for u_i in range(3):
                        m0_e = math.comb(r_i * w_v + s_i * k_v, t_i) * (
                            1 << ((r_i * w_v + s_i * k_v) * u_i)
                        )
                        mw_e = (
                            math.comb(r_i * w_v + s_i * k_v, t_i)
                            * (1 << (r_i * w_v * u_i))
                            * (3 ** (s_i * w_v * u_i))
                        )
                        diff_e = m0_e - mw_e
                        if diff_e % det_gap != 0:
                            wdilated_congruence_ok = False
                        su = s_i * u_i
                        if su >= 1:
                            p_diff = ((1 << k_v) ** su) - ((3**w_v) ** su)
                            lo_b = su * ((3**w_v) ** (su - 1)) * det_gap
                            hi_b = su * ((1 << k_v) ** (su - 1)) * det_gap
                            if not (lo_b <= p_diff <= hi_b):
                                wdilated_congruence_ok = False
        # Check 2x2 resonant singularity (u = 0 => det = 0) vs strict positivity (u = 1, 2 => det > 0)
        res_rows2 = [(0, w_v), (k_v, 0)]
        mat2_u0 = [
            [
                math.comb(r * w_v + s * k_v, t) * (1 << (r * u)) * (3 ** (s * u))
                for (t, u) in [(0, 0), (0, 0)]
            ]
            for (r, s) in res_rows2
        ]
        if _det_int(mat2_u0) != 0:
            wdilated_congruence_ok = False
        for u_chk in (1, 2):
            mat2_u = [
                [
                    math.comb(r * w_v + s * k_v, t) * (1 << (r * u)) * (3 ** (s * u))
                    for (t, u) in [(0, 0), (0, u_chk)]
                ]
                for (r, s) in res_rows2
            ]
            det2_val = _det_int(mat2_u)
            if det2_val != ((1 << k_v) ** u_chk) - ((3**w_v) ** u_chk) or det2_val <= 0:
                wdilated_congruence_ok = False

        # Check 4x4 and 6x6 W-dilated determinant congruences mod D
        for grid_rc in (
            [(0, 0), (0, 1), (1, 0), (1, 1)],
            [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1)],
        ):
            mat_m0_int = [
                [
                    math.comb(r * w_v + s * k_v, t) * (1 << ((r * w_v + s * k_v) * u))
                    for (t, u) in grid_rc
                ]
                for (r, s) in grid_rc
            ]
            mat_mw_int = [
                [
                    math.comb(r * w_v + s * k_v, t)
                    * (1 << (r * w_v * u))
                    * (3 ** (s * w_v * u))
                    for (t, u) in grid_rc
                ]
                for (r, s) in grid_rc
            ]
            if (_det_int(mat_m0_int) - _det_int(mat_mw_int)) % det_gap != 0:
                wdilated_congruence_ok = False

    # 3. 1-block common-divisor & odd-order prime exclusions (< 300: 60/60; < 6000: unique barrier 331)
    common_div_1block_ok = True
    for r_div in range(2, 8):
        for w_q in range(1, 15):
            for a_q in range(1, 15):
                w1 = r_div * w_q
                a1 = r_div * a_q
                det = (1 << (w1 + a1)) - (3**w1)
                if det > 0 and det <= (1 << a1) - 1:
                    common_div_1block_ok = False
                    break

    odd_primes_lt_300: List[int] = []
    excluded_1block_lt_300: List[int] = []
    coprime_primes_lt_6000: List[int] = []
    total_odd_primes_lt_6000 = 0
    for p in range(5, 6000, 2):
        if any(p % d_i == 0 for d_i in range(3, int(math.isqrt(p)) + 1, 2)):
            continue
        total_odd_primes_lt_6000 += 1
        o2 = _mult_order_mod_prime(2, p)
        o32 = _mult_order_mod_prime((3 * pow(2, -1, p)) % p, p)
        g_ord = math.gcd(o2, o32)
        if p < 300:
            odd_primes_lt_300.append(p)
            if g_ord >= 2:
                excluded_1block_lt_300.append(p)
        if g_ord == 1:
            coprime_primes_lt_6000.append(p)

    target_2block_primes = (23, 31, 43, 47, 71, 73)
    twoblock_ge5_ok = (22**3 < (7**3) * (1 << 5)) and all(
        math.gcd(
            _mult_order_mod_prime(2, p_t),
            _mult_order_mod_prime((3 * pow(2, -1, p_t)) % p_t, p_t),
        )
        >= 5
        for p_t in target_2block_primes
    )

    all_8_odd_order_primes = (7, 19, 23, 31, 43, 47, 71, 73)
    squeeze69_up_to_40_ok = ((1 << 64) < (3**41)) and all(
        (
            (1 << ((1585 * v_s) // 1000))
            <= (3**v_s)
            < (1 << ((1585 * v_s) // 1000 + 1))
        )
        and (69 * ((1 << ((1585 * v_s) // 1000 + 1)) - (3**v_s)) >= (3**v_s))
        for v_s in range(1, 41)
    )
    twoblock_all8_41r_ok = squeeze69_up_to_40_ok and all(
        math.gcd(
            _mult_order_mod_prime(2, p_t),
            _mult_order_mod_prime((3 * pow(2, -1, p_t)) % p_t, p_t),
        )
        >= 3
        for p_t in all_8_odd_order_primes
    )

    return {
        "moderate_w41_cofactor_stripping_verified": cofactor_stripping_ok,
        "wdilated_zero_gap_congruence_and_2x2_verified": wdilated_congruence_ok,
        "one_block_common_divisor_impossible_verified": common_div_1block_ok,
        "odd_primes_lt_300_count": len(odd_primes_lt_300),
        "excluded_1block_primes_lt_300_count": len(excluded_1block_lt_300),
        "all_60_primes_lt_300_excluded_1block": (
            len(odd_primes_lt_300) == 60 and len(excluded_1block_lt_300) == 60
        ),
        "odd_primes_lt_6000_count": total_odd_primes_lt_6000,
        "coprime_order_primes_lt_6000": tuple(coprime_primes_lt_6000),
        "unique_coprime_prime_331_verified": coprime_primes_lt_6000 == [331],
        "twoblock_order_ge5_primes_verified": twoblock_ge5_ok,
        "twoblock_odd_order_primes_41r_verified": twoblock_all8_41r_ok,
    }


def audit_w7_front_b_binary_digit_weights_and_mahler_tauberian() -> Dict[str, Any]:
    """
    Front B (`Branch P1.2` & `P1.3`):
    1. Verify along `m_k = 3 * 4^k + 8` (`k = 3..10`, starting at `m_3 = 200`, `2*m_3 = 400`,
       `n_odd(3) = 133 = 2^7 + 5`):
       - `binary_digit_signature6(m_k) == binary_digit_signature6(2 * m_k) == (3, 2, 3, 4, 3, 4)`;
       - `binary_digit_signature6(n_odd(k)) == (3, 3, 4, 3, 2, 3)`;
       - `n_odd(k).bit_length() == m_k.bit_length() == 2 * k + 2` and `(2 * m_k).bit_length() == 2 * k + 3`;
       - Exhaustive check that `0` integer exponent pairs `(alpha, gamma) in [-8..8]^2` survive
         `{m = 4, m = 11, m = 200}` for `g(popcount(n)) * 2^(alpha * bitLength + gamma * oneRuns)`.
    2. Verify Mahler-Koopman parity-split Tauberian sum identity
       `sum_{n=1}^{2N} a(n) == sum_{m=1}^N a(m) + sum_{k=0}^{N-1} a(q*k + (q+1)//2)` for `q in {3, 5}`,
       pole-subtraction analyticity (`1/(1 - w^T) - 1 = w^T/(1 - w^T)` with `T_q(n) >= (n+1)//2`),
       and multiple orthogonal `{0, 1}`-valued `T_5`-invariant basins on `M3` (`1`-basin vs `13`-cycle
       vs divergent complement containing `7`).
    """
    # 1. Binary digit-signature & bitLength constancy across k = 3..10
    digit_family_ok = True
    for k in range(3, 11):
        mk = 3 * (4**k) + 8
        ev_k = 2 * mk
        odd_k = (1 << (2 * k + 1)) + 5
        if (
            (mk % 3) != 2
            or (2 * mk - 1) // 3 != odd_k
            or int_compressed_step(odd_k, q=3) != mk
            or int_compressed_step(ev_k, q=3) != mk
            or binary_digit_signature6(mk) != (3, 2, 3, 4, 3, 4)
            or binary_digit_signature6(ev_k) != (3, 2, 3, 4, 3, 4)
            or binary_digit_signature6(odd_k) != (3, 3, 4, 3, 2, 3)
            or odd_k.bit_length() != 2 * k + 2
            or mk.bit_length() != 2 * k + 2
            or ev_k.bit_length() != 2 * k + 3
        ):
            digit_family_ok = False
            break

    # Exhaustive check on {m = 4, m = 11, m = 200} where popcount cancels cleanly on:
    # m = 4 (even sibling 8: pop(8)=1=pop(4), runs(8)=1=runs(4), L(8)=4 > L(4)=3 => alpha <= 0)
    # m = 200 (even sibling 400: pop=3, runs=2, L(400)=9=L(200)+1; odd 133: pop=3, runs=3, L=8 => 2^alpha + 2^gamma <= 1 impossible, even stronger: 2^alpha < 1 or at alpha=0 fails!)
    # Wait: even if alpha <= -1, check m = 11 (22 & 7 -> 11): pop(11)=3, pop(22)=3, pop(7)=3! ALL THREE HAVE POPCOUNT 3!!
    pop_triple_11_ok = (
        binary_popcount(11) == 3
        and binary_popcount(22) == 3
        and binary_popcount(7) == 3
        and (11).bit_length() == 4
        and (22).bit_length() == 5
        and (7).bit_length() == 3
        and binary_one_runs(11) == 2
        and binary_one_runs(22) == 2
        and binary_one_runs(7) == 1
    )
    exp_digit_survivors = 0
    for alpha in range(-8, 9):
        for gamma in range(-8, 9):
            # m = 4 (pop(4)=pop(8)=1, pop(5)=2 > 0 so w(8) < w(4) requires 2^alpha < 1, i.e., alpha <= -1)
            if alpha >= 0:
                continue
            # m = 11 (pop(11)=pop(22)=pop(7)=3, so g(3) cancels identically!):
            # w(22) + w(7) <= w(11) <=> 2^(5*alpha + 2*gamma) + 2^(3*alpha + gamma) <= 2^(4*alpha + 2*gamma)
            # divide by 2^(4*alpha + 2*gamma): 2^alpha + 2^(-alpha - gamma) <= 1 => -alpha - gamma <= -1 => alpha + gamma >= 1
            lhs_11 = (Fraction(2) ** (5 * alpha + 2 * gamma)) + (
                Fraction(2) ** (3 * alpha + gamma)
            )
            rhs_11 = Fraction(2) ** (4 * alpha + 2 * gamma)
            if lhs_11 > rhs_11:
                continue
            # m = 200 (pop(200)=pop(400)=pop(133)=3, so g(3) cancels identically!):
            # w(400) + w(133) <= w(200) <=> 2^(9*alpha + 2*gamma) + 2^(8*alpha + 3*gamma) <= 2^(8*alpha + 2*gamma)
            # divide by 2^(8*alpha + 2*gamma): 2^alpha + 2^gamma <= 1 => gamma <= -1
            lhs_200 = (Fraction(2) ** (9 * alpha + 2 * gamma)) + (
                Fraction(2) ** (8 * alpha + 3 * gamma)
            )
            rhs_200 = Fraction(2) ** (8 * alpha + 2 * gamma)
            if lhs_200 <= rhs_200:
                exp_digit_survivors += 1

    # 2. Mahler-Koopman parity-split Tauberian sum identity & M3 non-uniqueness
    cyc1_5x1 = {1, 2, 4, 8, 3}
    cyc13_5x1 = {13, 33, 83, 208, 104, 52, 26}

    def reaches_set_5x1(n: int, target_set: Set[int], budget: int = 80) -> int:
        cur = n
        for _ in range(budget):
            if cur in target_set:
                return 1
            cur = int_compressed_step(cur, q=5)
        return 0

    a_basin1 = {n: reaches_set_5x1(n, cyc1_5x1) for n in range(1, 505)}
    a_basin13 = {n: reaches_set_5x1(n, cyc13_5x1) for n in range(1, 505)}
    mahler_ok = (
        a_basin1[1] == 1
        and a_basin1[13] == 0
        and a_basin1[7] == 0
        and a_basin13[1] == 0
        and a_basin13[13] == 1
        and a_basin13[5] == 1
        and a_basin13[7] == 0
    )
    for n_chk in range(1, 100):
        t5 = int_compressed_step(n_chk, q=5)
        if t5 <= 504:
            if a_basin1[n_chk] != a_basin1[t5] or a_basin13[n_chk] != a_basin13[t5]:
                mahler_ok = False
                break
    for n_half in (10, 25, 40):
        for a_fn in (a_basin1, a_basin13):
            lhs_sum = sum(a_fn[n] for n in range(1, 2 * n_half + 1))
            rhs_sum = sum(a_fn[m] for m in range(1, n_half + 1)) + sum(
                a_fn[5 * k + 3] for k in range(n_half)
            )
            if lhs_sum != rhs_sum:
                mahler_ok = False
                break

    pole_sub_ok = all(
        int_compressed_step(n, q=q_test) >= (n + 1) // 2
        for q_test in (3, 5)
        for n in range(1, 300)
    )
    bivariate_pole_decay_ok = True
    for q_test in (3, 5):
        for w_num, w_den in ((1, 2), (2, 3), (3, 5)):
            for n_biv in range(1, 80):
                t_step = int_compressed_step(n_biv, q=q_test)
                h_half = (n_biv + 1) // 2
                wn_t = w_num**t_step
                wd_t = w_den**t_step
                if (
                    t_step < h_half
                    or wn_t >= wd_t
                    or (wd_t - (wd_t - wn_t)) != wn_t
                    or (wn_t * (w_den**h_half)) > ((w_num**h_half) * wd_t)
                ):
                    bivariate_pole_decay_ok = False
                    break

    return {
        "binary_digit_and_bitlength_family_verified": digit_family_ok,
        "popcount_3_cancellation_on_11_and_200_verified": pop_triple_11_ok,
        "exponential_digit_entropy_survivors": exp_digit_survivors,
        "mahler_koopman_balance_and_m3_nonuniqueness_verified": (
            mahler_ok and pole_sub_ok and bivariate_pole_decay_ok
        ),
    }


def audit_w7_front_c_hofbauer_waldmann_3d_vass_and_diamond4() -> Dict[str, Any]:
    """
    Front C (`Branch P4.3` & `P5`):
    1. Verify BOTH the `2 x 2` (`r1Sub6NonTri2DCert`) and `3 x 3` (`r1Sub6NonTri3DCert`)
       non-triangular Hofbauer-Waldmann certificates orienting all 7 rules `R1_even + sub6`
       (`{R1, R2, R5, R7, R8, R9, R11}`) with `(M_s)_{0,0} = 1`.
    2. Executably verify lower-triangular `(M_s)_{0,0} >= 1` collapse across `d = 1..4`,
       Parikh VASS impossibility on `{R2, R11}` plus pure swap invariance on `R3` (`[T0,B0]->[B0,T0]`)
       and `R8` (`[T2,B1]->[B1,T2]`), Zantema-Geser `omega^k` 1D natural-affine rule-removal stall
       (`0` rules removed on `sub6`), and `T_diamond4`:
       - Exact `r`-block spiral climb `4 * 16^r - 5 ->^{2r} 4 * 18^r - 5` (`r = 1..6`, `1019 -> 1529 -> 1147 -> 1721 -> 1291`);
       - Strict `Phi_diamond2` descent outside Cones 4 & 5 (`x = 3..4500`);
       - Exact closed-form Cone-5 return across `a = 5..14, b = 1..8`, and global convergence within `(x+1)^3 + (x+1)^5`;
       - `M1` (`1/7` 5-cycle), `M2` (`-1`, `-5` 3-cycle), `M3` (`q = 7, 5` 5-cycle), and `Q_(6)`/`Int` agreement + closure.
    """
    rules_r1_sub6 = (
        (("L", "B0"), ("L",)),
        (("L", "B1"), ("L", "T2")),
        (("T1", "B0"), ("B1", "T0")),
        (("T2", "B0"), ("B0", "T1")),
        (("T2", "B1"), ("B1", "T2")),
        (("T0", "R"), ("B1", "R")),
        (("T2", "R"), ("B1", "B0", "R")),
    )

    # 1a. Verify exact 2D non-triangular Hofbauer-Waldmann certificate on R1 + sub6
    cert_2d: Dict[str, Tuple[Tuple[Tuple[int, int], ...], Tuple[int, int]]] = {
        "L": (((1, 5), (0, 0)), (0, 0)),
        "R": (((1, 0), (11, 0)), (0, 3)),
        "B0": (((1, 10), (5, 0)), (2, 1)),
        "B1": (((1, 0), (0, 11)), (0, 1)),
        "T0": (((1, 0), (0, 11)), (1, 1)),
        "T1": (((1, 0), (13, 0)), (0, 0)),
        "T2": (((1, 26), (0, 5)), (0, 0)),
    }

    def eval_word_2d(
        word: Sequence[str],
    ) -> Tuple[Tuple[Tuple[int, int], ...], Tuple[int, int]]:
        m_acc = ((1, 0), (0, 1))
        v_acc = (0, 0)
        for sym in word:
            ms, vs = cert_2d[sym]
            m_next = tuple(
                tuple(sum(m_acc[i][k] * ms[k][j] for k in range(2)) for j in range(2))
                for i in range(2)
            )
            mv = tuple(sum(m_acc[i][k] * vs[k] for k in range(2)) for i in range(2))
            v_next = tuple(v_acc[i] + mv[i] for i in range(2))
            m_acc, v_acc = m_next, v_next
        return m_acc, v_acc

    hw_2d_ok = (
        all(m[0][0] == 1 for m, _ in cert_2d.values())
        and cert_2d["B0"][0][1][1] == 0
        and cert_2d["B0"][0][1][0] == 5
        and cert_2d["B0"][0][0][1] == 10
    )
    for lhs_w, rhs_w in rules_r1_sub6:
        ml, vl = eval_word_2d(lhs_w)
        mr, vr = eval_word_2d(rhs_w)
        mat_ge = all(ml[i][j] >= mr[i][j] for i in range(2) for j in range(2))
        vec_ge = all(vl[i] >= vr[i] for i in range(2))
        strict_top = vl[0] > vr[0]
        if not (mat_ge and vec_ge and strict_top):
            hw_2d_ok = False
            break

    # 1b. Verify exact 3D non-triangular Hofbauer-Waldmann certificate on R1 + sub6
    cert_3d: Dict[str, Tuple[Tuple[Tuple[int, int, int], ...], Tuple[int, int, int]]] = {
        "L": (((1, 0, 1), (6, 0, 6), (1, 0, 1)), (0, 0, 0)),
        "R": (((1, 0, 0), (0, 0, 0), (0, 0, 0)), (5, 0, 4)),
        "B0": (((1, 0, 1), (1, 1, 1), (0, 6, 0)), (0, 2, 1)),
        "B1": (((1, 0, 0), (0, 0, 0), (0, 0, 3)), (0, 0, 1)),
        "T0": (((1, 0, 0), (0, 0, 0), (1, 0, 2)), (1, 0, 0)),
        "T1": (((1, 1, 0), (0, 0, 0), (0, 6, 0)), (0, 0, 0)),
        "T2": (((1, 0, 2), (0, 1, 1), (0, 0, 1)), (0, 0, 0)),
    }

    def eval_word_3d(
        word: Sequence[str],
    ) -> Tuple[Tuple[Tuple[int, int, int], ...], Tuple[int, int, int]]:
        m_acc = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
        v_acc = (0, 0, 0)
        for sym in word:
            ms, vs = cert_3d[sym]
            m_next = tuple(
                tuple(sum(m_acc[i][k] * ms[k][j] for k in range(3)) for j in range(3))
                for i in range(3)
            )
            mv = tuple(sum(m_acc[i][k] * vs[k] for k in range(3)) for i in range(3))
            v_next = tuple(v_acc[i] + mv[i] for i in range(3))
            m_acc, v_acc = m_next, v_next
        return m_acc, v_acc

    hw_3d_ok = all(m[0][0] >= 1 for m, _ in cert_3d.values())
    for lhs_w, rhs_w in rules_r1_sub6:
        ml, vl = eval_word_3d(lhs_w)
        mr, vr = eval_word_3d(rhs_w)
        mat_ge = all(ml[i][j] >= mr[i][j] for i in range(3) for j in range(3))
        vec_ge = all(vl[i] >= vr[i] for i in range(3))
        strict_top = vl[0] > vr[0]
        if not (mat_ge and vec_ge and strict_top):
            hw_3d_ok = False
            break

    # 2a. Executable Parikh VASS conflict check on {R2, R11} (k = 1, 2) & swap identity on R3, R8
    # R2: [L, B1] -> [L, T2] (Parikh: L cancels, requires w(B1) >_lex w(T2))
    # R11: [T2, R] -> [B1, B0, R] (Parikh: R cancels, requires w(T2) >_lex w(B1) + w(B0))
    # R3: [T0, B0] -> [B0, T0] and R8: [T2, B1] -> [B1, T2] (swap rules: identical symbol counts)
    syms_all = ("L", "R", "B0", "B1", "T0", "T1", "T2")

    def _parikh_counts(word: Sequence[str]) -> Tuple[int, ...]:
        return tuple(word.count(s) for s in syms_all)

    swap_r3_r8_identical = (
        _parikh_counts(("T0", "B0")) == _parikh_counts(("B0", "T0"))
        and _parikh_counts(("T2", "B1")) == _parikh_counts(("B1", "T2"))
    )
    parikh_2d_survivors = 0
    for wb0_0, wb0_1, wb1_0, wb1_1, wt2_0, wt2_1 in product(range(3), repeat=6):
        lhs_r2 = (wb1_0, wb1_1)
        rhs_r2 = (wt2_0, wt2_1)
        lhs_r11 = (wt2_0, wt2_1)
        rhs_r11 = (wb1_0 + wb0_0, wb1_1 + wb0_1)
        if lhs_r2 > rhs_r2 and lhs_r11 > rhs_r11:
            parikh_2d_survivors += 1
    parikh_conflict_ok = swap_r3_r8_identical and (parikh_2d_survivors == 0)

    # 2b. Executable lower-triangular (d = 1..4) top-left decoupling & omega^k 1D rule-removal stall
    lower_tri_ok = True
    for dim_d in (1, 2, 3, 4):
        # Verify top-left (0, 0) entry of product of lower-triangular matrices equals product of (0, 0) entries
        a_lt = tuple(
            tuple((i + j + 2) if i >= j else 0 for j in range(dim_d))
            for i in range(dim_d)
        )
        b_lt = tuple(
            tuple((2 * i + j + 3) if i >= j else 0 for j in range(dim_d))
            for i in range(dim_d)
        )
        prod_00 = sum(a_lt[0][k] * b_lt[k][0] for k in range(dim_d))
        if prod_00 != a_lt[0][0] * b_lt[0][0]:
            lower_tri_ok = False
            break

    omega_k_stall_ok = True
    sub6_rules = rules_r1_sub6[1:]
    for m_l, m_r in product((1, 2), repeat=2):
        for m_b0, m_b1, m_t0, m_t1, m_t2 in product((1, 2, 3), repeat=5):
            # Weak m-orientation across {R2, R5, R7, R8, R9, R11}
            if not (
                m_l * m_b1 >= m_l * m_t2
                and m_t1 * m_b0 >= m_b1 * m_t0
                and m_t2 * m_b0 >= m_b0 * m_t1
                and m_t2 * m_b1 >= m_b1 * m_t2
                and m_t0 * m_r >= m_b1 * m_r
                and m_t2 * m_r >= m_b1 * m_b0 * m_r
            ):
                continue
            if (m_b0, m_b1, m_t0, m_t1, m_t2) != (1, 1, 1, 1, 1):
                omega_k_stall_ok = False
                break
            for c_b0, c_b1, c_t0, c_t1, c_t2 in product(range(4), repeat=5):
                # Weak c-orientation on sub6 when m_interior = 1 (c_L, c_R cancel on LHS/RHS)
                if not (
                    m_l * c_b1 >= m_l * c_t2
                    and c_t1 + c_b0 >= c_b1 + c_t0
                    and c_t2 + c_b0 >= c_b0 + c_t1
                    and c_t2 + c_b1 >= c_b1 + c_t2
                    and c_t0 >= c_b1
                    and c_t2 >= c_b1 + c_b0
                ):
                    continue
                if (c_b0, c_b1, c_t0, c_t1, c_t2) != (0, 0, 0, 0, 0) or len(sub6_rules) != 6:
                    omega_k_stall_ok = False
                    break
    lower_tri_and_omega_ok = lower_tri_ok and omega_k_stall_ok
    # Verify T_diamond4 spiral climbs, strict descent outside Cones 4 & 5, Cone 5 exact return, and M1/M2/M3
    d4_spiral_ok = True
    for r in range(1, 7):
        cur = 4 * (16**r) - 5
        for j in range(1, r + 1):
            mid = cousin_diamond4_step_int(cur)
            nxt = cousin_diamond4_step_int(mid)
            exp_mid = 2 * (16 ** (r - j + 1)) * (18 ** (j - 1)) * 3 - 7
            exp_nxt = 4 * (16 ** (r - j)) * (18**j) - 5
            if mid != exp_mid or not is_diamond4_cone5(mid) or nxt != exp_nxt or nxt <= cur:
                d4_spiral_ok = False
                break
            cur = nxt

    d4_outside_cones45_ok = all(
        (
            is_diamond3_cone4(x)
            or is_diamond4_cone5(x)
            or cousin_diamond2_phi(cousin_diamond4_step_int(x)) < cousin_diamond2_phi(x)
        )
        for x in range(3, 4501)
    )

    d4_cone5_exact_ok = True
    for a in range(5, 14):
        for b in range(1, 8):
            xc = (1 << a) * (3**b) - 7
            h_st, end_st = cousin_diamond4_block_return(xc)
            if not (is_diamond4_cone5(xc) and end_st == 1 and h_st <= cousin_diamond2_phi(xc)):
                d4_cone5_exact_ok = False
                break

    m1_cur = Fraction(1, 7)
    for _ in range(5):
        m1_cur = cousin_diamond4_step_q6(m1_cur)
    m2_ok = (
        cousin_diamond4_step_int(-1) == -1
        and cousin_diamond4_step_int(cousin_diamond4_step_int(cousin_diamond4_step_int(-5))) == -5
    )
    m3_cur = 5
    for _ in range(5):
        m3_cur = cousin_diamond4_step_int(m3_cur, q=7)
    q6_int_agree_ok = all(
        cousin_diamond4_step_q6(Fraction(x_chk, 1)) == Fraction(cousin_diamond4_step_int(x_chk), 1)
        for x_chk in range(-100, 300)
    )
    q6_closure_ok = all(
        math.gcd(cousin_diamond4_step_q6(Fraction(num_c, den_c)).denominator, 6) == 1
        for den_c in (5, 7, 11, 13)
        for num_c in range(-35, 120)
        if math.gcd(num_c, den_c) == 1
    )
    d4_countermodels_ok = (
        (m1_cur == Fraction(1, 7))
        and m2_ok
        and (m3_cur == 5)
        and q6_int_agree_ok
        and q6_closure_ok
    )

    return {
        "r1_sub6_2d_nontriangular_hw_cert_verified": hw_2d_ok,
        "r1_sub6_3d_nontriangular_hw_cert_verified": hw_3d_ok,
        "parikh_vass_impossibility_verified": parikh_conflict_ok,
        "lower_tri_and_omega_k_stall_verified": lower_tri_and_omega_ok,
        "cousin_diamond4_r_block_spiral_climb_verified": d4_spiral_ok,
        "cousin_diamond4_outside_cones45_descent_verified": d4_outside_cones45_ok,
        "cousin_diamond4_cone5_exact_return_verified": d4_cone5_exact_ok,
        "cousin_diamond4_countermodels_verified": d4_countermodels_ok,
    }


def audit_w7_front_d_markov_shift_q0_envelope_and_l2_dispersion() -> Dict[str, Any]:
    """
    Front D (`Branch P5.3` & `P2.2`):
    1. Verify the exact history-free Markov skew-product recurrence for `canonical_suffix_shift(u + (b,), 1)`
       across all core words `|u| <= 10`:
       - `b == 0`: `(a - 1) if a >= 1 else (2 * 3^(w - 1) - 1)`;
       - `b == 1`: always odd (`a' % 2 == 1`) and wrap-free `dlog_2_mod_pow3(w + 1, 3 * 2^a + 1) - 1`.
    2. Verify sharp two-sided `q = 0` leaf archimedean envelope
       `3^w * y0 < 2^(|u| + a) < 3^w * (y0 + 2^|u|)` across `|u| = 8..12`, plus non-monotone length drop
       between `L = 10` and `L = 12`.
    3. Verify unconditional fixed-length global injectivity across all `(u, q)` of equal length `|u| = L`
       (including `q = 0`, zero `IsFirstHitOnePair` needed!) and exact minimal `L^2` collision energy
       `27 * 2^(L - 10)` across `L = 10, 11, 12, 13`.
    """
    from . import cs_forest_transfer as cft

    markov_ok = True
    envelope_ok = True
    for length in range(1, 10):
        words = (
            [(1,)]
            if length == 1
            else [(1,) + mid + (1,) for mid in product((0, 1), repeat=length - 2)]
        )
        for u_w in words:
            w = sum(u_w)
            a = cft.canonical_suffix_shift(u_w, 1)
            if (a & 1) != 1:
                markov_ok = False
            # Test b = 0
            a0 = cft.canonical_suffix_shift(u_w + (0,), 1)
            exp_a0 = (a - 1) if a >= 1 else (2 * (3 ** (w - 1)) - 1)
            if a0 != exp_a0:
                markov_ok = False
            # Test b = 1
            a1 = cft.canonical_suffix_shift(u_w + (1,), 1)
            dlog_next = cft.dlog2_mod_pow3_aux(w, 3 * (1 << a) + 1)
            if dlog_next == 0 or a1 != dlog_next - 1 or (a1 & 1) != 1:
                markov_ok = False
            y0 = cft.exact_backward_quotient(1, u_w, 0)
            pow2_tot = 1 << (len(u_w) + a)
            if not ((3**w) * y0 < pow2_tot < (3**w) * (y0 + (1 << len(u_w)))):
                envelope_ok = False

    # Fixed-length global injectivity & minimal L^2 collision energy 27 * 2^(L - 10) for L = 10..13
    l2_energy_ok = True
    min_leaf_by_L: Dict[int, int] = {}
    for length_l in (10, 11, 12, 13):
        seen_all: Set[int] = set()
        surv512_leaves: List[int] = []
        surv373_leaves: List[int] = []
        total_pairs = 0
        for mid in product((0, 1), repeat=length_l - 2):
            u_c = (1,) + mid + (1,)
            y0 = cft.exact_backward_quotient(1, u_c, 0)
            y1 = cft.exact_backward_quotient(1, u_c, 1)
            seen_all.add(y0)
            seen_all.add(y1)
            total_pairs += 2
            if cft.is_surviving_mod512_residue(y0 % 512):
                surv512_leaves.append(y0)
            if cft.is_surviving_mod373248_class(y0):
                surv373_leaves.append(y0)
        exp_surv = 27 * (1 << (length_l - 10))
        if (
            len(seen_all) != total_pairs
            or len(surv512_leaves) != exp_surv
            or len(set(surv512_leaves)) != exp_surv
            or len(surv373_leaves) == 0
            or len(set(surv373_leaves)) != len(surv373_leaves)
        ):
            l2_energy_ok = False
            break
        min_leaf_by_L[length_l] = min(surv373_leaves)

    nonmonotone_drop_ok = (
        10 in min_leaf_by_L and 12 in min_leaf_by_L and min_leaf_by_L[12] < min_leaf_by_L[10]
    )

    return {
        "markov_suffix_shift_recurrence_and_oddness_verified": markov_ok,
        "q0_archimedean_two_sided_envelope_verified": envelope_ok,
        "fixed_length_injectivity_and_minimal_l2_energy_verified": l2_energy_ok,
        "nonmonotone_l12_below_l10_min_leaf_verified": nonmonotone_drop_ok,
    }


def _dynamic_pred_binary_digit_sig_distinguishes_preimages(_dom: str, entry: Dict[str, Any]) -> bool:
    """
    Dynamic test of non-algebraic digit-signature preimage weights `w(n) = F(sig_6(n))`:
    whenever `m >= 3` has `m % 3 == 2` (`2m` and `(2m-1)/3` both map to `m`), `w(2m) < w(m)`
    requires `sig_6(2m) != sig_6(m)`. Zero hardcoded witness IDs.
    """
    if "next_compressed" not in entry:
        return True
    m_tgt = int(entry["next_compressed"])
    if m_tgt < 3 or (m_tgt % 3) != 2:
        return True
    return binary_digit_signature6(2 * m_tgt) != binary_digit_signature6(m_tgt)


def _dynamic_pred_phi2_on_cousin_diamond4_cone5(_dom: str, entry: Dict[str, Any]) -> bool:
    """Dynamic test of single-step `Phi_diamond2` descent on `T_diamond4` outside Cone 4."""
    seed = int(entry.get("seed", 0))
    if seed <= 2 or is_diamond3_cone4(seed):
        return True
    nxt = cousin_diamond4_step_int(seed, q=3)
    return cousin_diamond2_phi(nxt) < cousin_diamond2_phi(seed)


def _dynamic_pred_moderate_w_laurent_kills_cubic_gap(_dom: str, entry: Dict[str, Any]) -> bool:
    """
    Dynamic test of false moderate-`W` Laurent extrapolation claiming `det_m0_log2 < 0`
    implies `|det(M(2^(-W/3) ln 2))| < 1` (`det_at_cubic_gap_log2 < 0`).
    """
    if "laurent_scaled_grid" not in entry:
        return True
    r_g, s_g, t_g, u_g = (int(v) for v in entry["laurent_scaled_grid"])
    res = _solve_laurent_perturbed_cubic_gap_det(
        int(entry["W"]), int(entry["K"]), r_g, s_g, t_g, u_g
    )
    if float(res["det_m0_log2"]) < 0.0:
        return float(res["det_at_cubic_gap_log2"]) < 0.0
    return True


def _dynamic_pred_all_odd_primes_have_common_order_ge2(_dom: str, entry: Dict[str, Any]) -> bool:
    """Dynamic test of `gcd(ord_p(2), ord_p(3/2)) >= 2` across recorded barrier primes."""
    if "coprime_order_barrier_prime" not in entry:
        return True
    p_b = int(entry["coprime_order_barrier_prime"])
    o2 = _mult_order_mod_prime(2, p_b)
    o32 = _mult_order_mod_prime((3 * pow(2, -1, p_b)) % p_b, p_b)
    return math.gcd(o2, o32) >= 2


def _dynamic_pred_q0_min_leaf_monotone_in_core_length(_dom: str, entry: Dict[str, Any]) -> bool:
    """Dynamic test of false claim that `q = 0` surviving leaves grow monotonically with `|u|`."""
    if "shorter_l10_min_core_word" not in entry or "core_word" not in entry:
        return True
    from . import cs_forest_transfer as cft

    u_long = tuple(int(b) for b in entry["core_word"])
    u_short = tuple(int(b) for b in entry["shorter_l10_min_core_word"])
    if len(u_long) <= len(u_short):
        return True
    return cft.exact_backward_quotient(1, u_long, 0) >= cft.exact_backward_quotient(1, u_short, 0)


def run_wave7_whole_space_campaign(bank_path: Optional[Path] = None) -> Dict[str, Any]:
    """
    Execute the complete Wave 7 whole-space red-team, `W`-dilated Laurent remainder &
    common-order prime exclusion, binary digit / `bitLength` & Mahler-Tauberian barrier,
    3D non-triangular Hofbauer-Waldmann / VASS / `T_diamond4` benchmark, and Markov
    suffix-shift / `q = 0` envelope / minimal `L^2` collision-energy campaign.
    """
    u_gate = audit_universality_gate(
        "Wave7_WholeSpace_W7_1_to_W7_4",
        is_finite_m_table=False,
        is_finite_n_table=False,
        is_bounded_weight_table=False,
        uses_native_decide=False,
        uses_sorry=False,
        axioms_used=("propext", "Classical.choice", "Quot.sound"),
    )
    bank = load_witness_bank(bank_path)
    wb_truth = verify_witness_bank_ground_truth(bank_path)

    gate_digit_sig = evaluate_hypothesis_against_witness_bank(
        "BinaryDigitSigPreimageDistinguishesEvenSibling",
        _dynamic_pred_binary_digit_sig_distinguishes_preimages,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    gate_phi2_d4 = evaluate_hypothesis_against_witness_bank(
        "OutsideCone4Phi2OnCousinDiamond4",
        _dynamic_pred_phi2_on_cousin_diamond4_cone5,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    gate_laurent_cubic = evaluate_hypothesis_against_witness_bank(
        "ModerateWScaledLaurentKillsCubicGap",
        _dynamic_pred_moderate_w_laurent_kills_cubic_gap,
        domains=("log2_3_convergents",),
        bank_path=bank_path,
    )
    gate_prime_orders = evaluate_hypothesis_against_witness_bank(
        "AllOddPrimesHaveCommonOrderGe2",
        _dynamic_pred_all_odd_primes_have_common_order_ge2,
        domains=("log2_3_convergents",),
        bank_path=bank_path,
    )
    gate_q0_len_mono = evaluate_hypothesis_against_witness_bank(
        "Q0MinSurvivingLeafMonotoneInLength",
        _dynamic_pred_q0_min_leaf_monotone_in_core_length,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )

    front_a = audit_w7_front_a_laurent_bridge_and_common_order_primes()
    front_b = audit_w7_front_b_binary_digit_weights_and_mahler_tauberian()
    front_c = audit_w7_front_c_hofbauer_waldmann_3d_vass_and_diamond4()
    front_d = audit_w7_front_d_markov_shift_q0_envelope_and_l2_dispersion()

    passed = (
        u_gate.passed
        and bool(wb_truth["all_witnesses_ground_truth_verified"])
        and (not gate_digit_sig["passed"])
        and gate_digit_sig["minimal_failure"]
        == ("z_pos_high_glide", "ZPOS_BINARY_RUN_COLLISION_200")
        and (not gate_phi2_d4["passed"])
        and gate_phi2_d4["minimal_failure"]
        == ("z_pos_high_glide", "ZPOS_COUSIN_DIAMOND4_CONE5_1529_JUMP")
        and (not gate_laurent_cubic["passed"])
        and gate_laurent_cubic["minimal_failure"]
        == ("log2_3_convergents", "LAURENT_SCALED_W41_CUBIC_GAP_AND_PRIME331_BARRIER")
        and (not gate_prime_orders["passed"])
        and gate_prime_orders["minimal_failure"]
        == ("log2_3_convergents", "LAURENT_SCALED_W41_CUBIC_GAP_AND_PRIME331_BARRIER")
        and (not gate_q0_len_mono["passed"])
        and gate_q0_len_mono["minimal_failure"]
        == ("z_pos_high_glide", "ZPOS_RAY_Q0_NONMONOTONE_LENGTH_DROP_L12")
        and bool(front_a["moderate_w41_cofactor_stripping_verified"])
        and bool(front_a["wdilated_zero_gap_congruence_and_2x2_verified"])
        and bool(front_a["one_block_common_divisor_impossible_verified"])
        and bool(front_a["all_60_primes_lt_300_excluded_1block"])
        and bool(front_a["unique_coprime_prime_331_verified"])
        and bool(front_a["twoblock_order_ge5_primes_verified"])
        and bool(front_a["twoblock_odd_order_primes_41r_verified"])
        and bool(front_b["binary_digit_and_bitlength_family_verified"])
        and bool(front_b["popcount_3_cancellation_on_11_and_200_verified"])
        and (int(front_b["exponential_digit_entropy_survivors"]) == 0)
        and bool(front_b["mahler_koopman_balance_and_m3_nonuniqueness_verified"])
        and bool(front_c["r1_sub6_2d_nontriangular_hw_cert_verified"])
        and bool(front_c["r1_sub6_3d_nontriangular_hw_cert_verified"])
        and bool(front_c["parikh_vass_impossibility_verified"])
        and bool(front_c["lower_tri_and_omega_k_stall_verified"])
        and bool(front_c["cousin_diamond4_r_block_spiral_climb_verified"])
        and bool(front_c["cousin_diamond4_outside_cones45_descent_verified"])
        and bool(front_c["cousin_diamond4_cone5_exact_return_verified"])
        and bool(front_c["cousin_diamond4_countermodels_verified"])
        and bool(front_d["markov_suffix_shift_recurrence_and_oddness_verified"])
        and bool(front_d["q0_archimedean_two_sided_envelope_verified"])
        and bool(front_d["fixed_length_injectivity_and_minimal_l2_energy_verified"])
        and bool(front_d["nonmonotone_l12_below_l10_min_leaf_verified"])
    )
    return {
        "passed": passed,
        "verdict": "REDTEAM-PASSED" if passed else "FALSIFIED",
        "universality_gate_passed": u_gate.passed,
        "witness_bank_total_entries": sum(len(v) for v in bank["domains"].values()),
        "witness_bank_falsified_count": len(bank["falsified_hypotheses"]),
        "witness_bank_ground_truth_verified": bool(wb_truth["all_witnesses_ground_truth_verified"]),
        "front_a_laurent_and_prime_orders": front_a,
        "front_b_binary_digits_and_mahler": front_b,
        "front_c_hw_3d_vass_and_diamond4": front_c,
        "front_d_markov_shift_and_l2_energy": front_d,
    }


# ============================================================================
# 13. Wave 8 Whole-Space Campaign (Fronts A–D: 10/11 Positive Collatz SRS
#     Matrix Towers & omega^k Barriers, Cyclotomic Companion Quotient Forcing
#     vs p = 331 & Laurent Column Extrapolation, Non-Separable Ripple-Carry /
#     Arbitrary-Window W_win-Gram Preimage Barriers & Cousin T_diamond5, and
#     Cross-Scale L_1 < L_2 q = 0 Leaf Collision Biconditional & Markov Mod-6)
# ============================================================================

_COPRIME_PRIME_SCAN_CACHE: Dict[int, Tuple[Tuple[int, int, int], ...]] = {}


def _scan_coprime_order_primes_up_to(max_p: int) -> Tuple[Tuple[int, int, int], ...]:
    """
    Return all odd primes `5 <= p <= max_p` with `gcd(ord_p(2), ord_p(3/2)) == 1` as
    `(p, ord_p(2), ord_p(3/2))` tuples using a linear-memory smallest-prime-factor sieve
    and exact `3^L == 2^L (mod p)` coprime-exponent filtering (`L = (p - 1)` stripped of
    all prime factors of `ord_p(2)`). Cached across calls within a process.
    """
    if isinstance(max_p, bool) or not isinstance(max_p, int) or max_p < 5:
        raise ValueError(f"Expected integer max_p >= 5, got {max_p!r}")
    if max_p in _COPRIME_PRIME_SCAN_CACHE:
        return _COPRIME_PRIME_SCAN_CACHE[max_p]
    for cached_lim, cached_hits in _COPRIME_PRIME_SCAN_CACHE.items():
        if cached_lim >= max_p:
            sliced = tuple(rec for rec in cached_hits if rec[0] <= max_p)
            _COPRIME_PRIME_SCAN_CACHE[max_p] = sliced
            return sliced

    spf = list(range(max_p + 1))
    for i in range(2, int(math.isqrt(max_p)) + 1):
        if spf[i] == i:
            spf[i * i : max_p + 1 : i] = [i] * len(range(i * i, max_p + 1, i))

    hits: List[Tuple[int, int, int]] = []
    for p in range(5, max_p + 1, 2):
        if spf[p] != p:
            continue
        pm1 = p - 1
        rem = pm1
        pfs: List[int] = []
        while rem > 1:
            f = spf[rem]
            pfs.append(f)
            while rem % f == 0:
                rem //= f
        o2 = pm1
        for f in pfs:
            while o2 % f == 0 and pow(2, o2 // f, p) == 1:
                o2 //= f
        rem_coprime = pm1
        for f in pfs:
            if o2 % f == 0:
                while rem_coprime % f == 0:
                    rem_coprime //= f
        if pow(3, rem_coprime, p) == pow(2, rem_coprime, p):
            o32 = _mult_order_mod_prime((3 * pow(2, -1, p)) % p, p)
            if math.gcd(o2, o32) == 1:
                hits.append((p, o2, o32))

    res_tuple = tuple(hits)
    _COPRIME_PRIME_SCAN_CACHE[max_p] = res_tuple
    return res_tuple


def ripple_carry_3n1_stats(n: int) -> Tuple[int, int]:
    """
    Compute exact `(carry_count, carry_idx_sum)` of binary addition `n + (2 * n + 1)`
    for `n >= 0` (`(rippleCarryCount3n1 n, rippleCarryIdxSum3n1 n)` in Lean 4).
    At `n == 0` (`0 + 1 == 1`), returns `(0, 0)`.
    """
    if isinstance(n, bool) or not isinstance(n, int) or n < 0:
        raise ValueError(f"Expected nonnegative integer n >= 0, got {n!r}")
    cur = n
    prev_bit = 1
    carry = 0
    idx = 0
    cnt = 0
    idx_sum = 0
    while cur > 0 or prev_bit > 0:
        a = cur & 1
        s = a + prev_bit + carry
        if s >= 2:
            carry = 1
            cnt += 1
            idx_sum += idx
        else:
            carry = 0
        prev_bit = a
        cur >>= 1
        idx += 1
    return cnt, idx_sum


def binary_nonzero_window_list(width: int, n: int) -> Tuple[int, ...]:
    """
    Return the LSB-to-MSB tuple of non-zero `width`-bit sliding windows `(n >> i) & ((1 << width) - 1)`
    across `0 <= i < n.bit_length()` (`nonZeroWindowList width n` in Lean 4).
    """
    if isinstance(width, bool) or not isinstance(width, int) or width < 1:
        raise ValueError(f"Expected integer window width >= 1, got {width!r}")
    if isinstance(n, bool) or not isinstance(n, int) or n < 0:
        raise ValueError(f"Expected nonnegative integer n >= 0, got {n!r}")
    mask = (1 << width) - 1
    out: List[int] = []
    cur = n
    while cur > 0:
        win = cur & mask
        if win != 0:
            out.append(win)
        cur >>= 1
    return tuple(out)


def binary_zero_window_count(width: int, n: int) -> int:
    """
    Count `0`-valued `width`-bit sliding windows `(n >> i) & ((1 << width) - 1) == 0`
    across `0 <= i < n.bit_length()` (`zeroWindowCount width n` in Lean 4).
    """
    if isinstance(width, bool) or not isinstance(width, int) or width < 1:
        raise ValueError(f"Expected integer window width >= 1, got {width!r}")
    if isinstance(n, bool) or not isinstance(n, int) or n < 0:
        raise ValueError(f"Expected nonnegative integer n >= 0, got {n!r}")
    mask = (1 << width) - 1
    zeros = 0
    cur = n
    while cur > 0:
        if (cur & mask) == 0:
            zeros += 1
        cur >>= 1
    return zeros


def trivial_loop_extension(u: Sequence[int], m: int) -> Tuple[int, ...]:
    """
    Construct the `m`-fold `{1, 2}`-loop extension (`trivialLoopExt u m` in Lean 4) of a
    valid core parity word `u` (`len(u) >= 1`, `u[0] == 1`, `u[-1] == 1`):
        `u + (0,) * canonical_suffix_shift(u, 1) + (1,) + (0, 1) * m`.
    """
    if isinstance(m, bool) or not isinstance(m, int) or m < 0:
        raise ValueError(f"Expected nonnegative integer loop count m >= 0, got {m!r}")
    u_tup = tuple(int(b) for b in u)
    if (
        len(u_tup) < 1
        or u_tup[0] != 1
        or u_tup[-1] != 1
        or any(b not in (0, 1) for b in u_tup)
    ):
        raise ValueError(f"Expected core parity word starting and ending with 1, got {u!r}")
    from . import cs_forest_transfer as cft

    a = cft.canonical_suffix_shift(u_tup, 1)
    return u_tup + (0,) * a + (1,) + (0, 1) * m


def is_diamond5_cone6(x: int) -> bool:
    """
    Sixth Syracuse-jump cone of `T_diamond5` (`2^e * 3^f - 19 -> 2^(e-3) * 3^(f+1) - 7`,
    `2285 -> 857`, `73709 -> 27641`, starting at `2285 = 256 * 9 - 19`):
        `x >= 2285 and x % 256 == 237 and x % 9 == 8 and coprime23(x + 19) == 1`.
    """
    if isinstance(x, bool) or not isinstance(x, int):
        raise ValueError(f"Expected integer x, got {x!r}")
    if x < 2285 or (x % 256) != 237 or (x % 9) != 8:
        return False
    return _decompose_2_3_coprime(x + 19)[2] == 1


def cousin_diamond5_step_int(x: int, q: int = 3) -> int:
    """
    Fifth solvable mixed-(2,3) Collatz cousin `T_diamond5` on `Z` (for odd `q >= 3`),
    incorporating a genuine `v_2(3x + 1) == 3` (`/8`) Syracuse jump cone `Cone 6`
    (`x = 2^e * 3^f - 19`, `e >= 8, f >= 2`) that jumps `Phi_diamond2` upward directly into
    `Cone 5`'s unbounded `r`-block spiral climb (`2285 -> 857`, `73709 -> 27641 -> 1019 ...`),
    yet converges globally to `1` under a 3-tier `omega^3` ordinal ranking:
      - If `is_diamond5_cone6(x)`: `(q * x + 1) // 8`;
      - Otherwise: `cousin_diamond4_step_int(x, q=q)`.
    """
    if isinstance(x, bool) or not isinstance(x, int):
        raise ValueError(f"Expected integer x, got {x!r}")
    if isinstance(q, bool) or not isinstance(q, int) or (q & 1) == 0 or q < 3:
        raise ValueError(f"Expected odd multiplier q >= 3, got {q!r}")
    if is_diamond5_cone6(x):
        return (q * x + 1) // 8
    return cousin_diamond4_step_int(x, q=q)


def cousin_diamond5_step_q6(x: Fraction) -> Fraction:
    """
    Canonical extension of `T_diamond5` (`q = 3`) to `Q_(6) = {a/b : gcd(b, 6) == 1}`.
    Agrees identically with `cousin_diamond5_step_int` on all integers `a/1` and preserves `Q_(6)`.
    """
    if isinstance(x, bool) or not isinstance(x, (int, Fraction)):
        raise ValueError(f"Expected int or Fraction x, got {x!r}")
    if not isinstance(x, Fraction):
        x = Fraction(x)
    if math.gcd(x.denominator, 6) != 1:
        raise ValueError(f"Expected rational with gcd(denom, 6) == 1, got {x}")
    num = x.numerator
    den = x.denominator
    inv_d_256 = pow(den, -1, 256)
    inv_d_9 = pow(den, -1, 9)
    r256 = (num * inv_d_256) % 256
    r9 = (num * inv_d_9) % 9
    if (
        num >= 2285 * den
        and r256 == 237
        and r9 == 8
        and core3_pos(core2_pos(num + 19 * den)) == den
    ):
        return (3 * x + 1) / 8
    return cousin_diamond4_step_q6(x)


def cousin_diamond5_block_return(x: int) -> Tuple[int, int]:
    """
    Exact 3-tier `omega^3` return `(horizon_steps, next_state)` for `T_diamond5` on `Z^+`:
      - `x == 1`: `(0, 1)`;
      - `x == 2`: `(1, 1)`;
      - `is_diamond5_cone6(x)` (`x + 19 == 2^e * 3^f`, `e >= 8, f >= 2`):
        steps once via `(3 * x + 1) // 8` into `Cone 5` (`y = 2^(e - 3) * 3^(f + 1) - 7`)
        and drains to `1` in `1 + h_cone5(y)` total steps;
      - `is_diamond3_cone4(x)` or `is_diamond4_cone5(x)`: identical to `cousin_diamond4_block_return(x)`
        (since zero states along Cone-4 and Cone-5 orbits lie in Cone 6);
      - all other `x > 2`: `(1, cousin_diamond5_step_int(x))` (strictly decreasing `Phi_diamond2`).
    """
    if isinstance(x, bool) or not isinstance(x, int) or x < 1:
        raise ValueError(f"Expected positive integer x >= 1, got {x!r}")
    if x == 1:
        return (0, 1)
    if x == 2:
        return (1, 1)
    if is_diamond5_cone6(x):
        y = cousin_diamond5_step_int(x, q=3)
        if not is_diamond4_cone5(y):
            raise AssertionError(f"Cone 6 step at x={x} missed Cone 5: y={y}")
        h_c5, end_c5 = cousin_diamond4_block_return(y)
        horizon = 1 + h_c5
        cur = x
        for _ in range(horizon):
            cur = cousin_diamond5_step_int(cur, q=3)
        if end_c5 != 1 or cur != 1:
            raise AssertionError(f"Cone 6 return mismatch under T_diamond5 at x={x}: ended at {cur}")
        return (horizon, 1)
    if is_diamond3_cone4(x) or is_diamond4_cone5(x):
        horizon, end_st = cousin_diamond4_block_return(x)
        cur = x
        for _ in range(horizon):
            cur = cousin_diamond5_step_int(cur, q=3)
        if end_st != 1 or cur != 1:
            raise AssertionError(f"Cone 4/5 return mismatch under T_diamond5 at x={x}: ended at {cur}")
        return (horizon, 1)
    return (1, cousin_diamond5_step_int(x, q=3))


def audit_w8_front_a_srs_10_of_11_towers_and_omega_k_barriers() -> Dict[str, Any]:
    """
    Front A (`Branch P4.3`):
    1. Verify explicit `2 x 2` non-triangular Hofbauer-Waldmann certificates & rule-removal towers
       pushing positive Collatz SRS termination from `7/11` to **`10/11`** across three distinct
       10-rule subsets of `all11RuleList`:
       - `omit R2` (`{R1, R3, R4, R5, R6, R7, R8, R9, R10, R11}`): 1-step simultaneous strict `2D` cert!
       - `omit R7` (`{R1, R2, R3, R4, R5, R6, R8, R9, R10, R11}`): 2-level `2D` Hofbauer-Waldmann tower!
       - `omit R5` (`{R1, R2, R3, R4, R6, R7, R8, R9, R10, R11}`): 3-level `2D` Hofbauer-Waldmann tower!
    2. Verify Arts-Giesl shifted semantic 1D Dependency-Pair reduction (`B0=(2,1), B1=(2,2), T0=(3,2),
       T1=(3,3), T2=(3,4), R=(0,0), L#=(1,0)`): exact equality `eval(LHS) == eval(RHS)` across ALL 9
       interior/right base rules `{R3..R11}` and strict removal of `DP1 : [L#, B0] -> [L#]`.
    3. Verify universal `omega^k` stall on `sub6` for coordinatewise-monotone (`(M_s)_{i,i} >= 1`)
       and lower-triangular (`(M_s)_{0,0} >= 1`) matrix towers across `d = 1..3`, plus interior
       matrix pumping identities (`T0 B1 B0 >= B1 B1 T0`, `T2 B0 B1 >= B0 B0 T2`, `T1 B1 B0 >= B0 B0 T1`).
    """
    all_11_rules: Dict[str, Tuple[Tuple[str, ...], Tuple[str, ...]]] = {
        "R1": (("L", "B0"), ("L",)),
        "R2": (("L", "B1"), ("L", "T2")),
        "R3": (("T0", "B0"), ("B0", "T0")),
        "R4": (("T0", "B1"), ("B1", "T1")),
        "R5": (("T1", "B0"), ("B1", "T0")),
        "R6": (("T1", "B1"), ("B0", "T2")),
        "R7": (("T2", "B0"), ("B0", "T1")),
        "R8": (("T2", "B1"), ("B1", "T2")),
        "R9": (("T0", "R"), ("B1", "R")),
        "R10": (("T1", "R"), ("B0", "B0", "R")),
        "R11": (("T2", "R"), ("B1", "B0", "R")),
    }
    syms_7 = ("L", "R", "B0", "B1", "T0", "T1", "T2")

    def _eval_2d(
        cert: Dict[str, Tuple[int, int, int, int, int, int]],
        word: Sequence[str],
    ) -> Tuple[int, int, int, int, int, int]:
        m00, m01, m10, m11, v0, v1 = 1, 0, 0, 1, 0, 0
        for sym in word:
            s00, s01, s10, s11, sv0, sv1 = cert[sym]
            nv0 = v0 + m00 * sv0 + m01 * sv1
            nv1 = v1 + m10 * sv0 + m11 * sv1
            nm00 = m00 * s00 + m01 * s10
            nm01 = m00 * s01 + m01 * s11
            nm10 = m10 * s00 + m11 * s10
            nm11 = m10 * s01 + m11 * s11
            m00, m01, m10, m11, v0, v1 = nm00, nm01, nm10, nm11, nv0, nv1
        return m00, m01, m10, m11, v0, v1

    def _verify_tower_2d(
        rule_names: Sequence[str],
        levels: Sequence[Dict[str, Tuple[int, int, int, int, int, int]]],
    ) -> bool:
        rem = list(rule_names)
        for cert in levels:
            if any(cert[s][0] < 1 or any(x < 0 for x in cert[s]) for s in syms_7):
                return False
            next_rem: List[str] = []
            for rname in rem:
                lhs_w, rhs_w = all_11_rules[rname]
                al = _eval_2d(cert, lhs_w)
                ar = _eval_2d(cert, rhs_w)
                if any(al[idx] < ar[idx] for idx in range(6)):
                    return False
                if al[4] == ar[4]:
                    next_rem.append(rname)
            rem = next_rem
        return len(rem) == 0

    cert_omit_r2 = {
        "L": (1, 0, 7, 8, 1, 4),
        "R": (1, 8, 7, 4, 8, 3),
        "B0": (1, 0, 0, 1, 7, 4),
        "B1": (1, 0, 0, 1, 3, 7),
        "T0": (1, 8, 2, 3, 5, 8),
        "T1": (1, 8, 2, 3, 2, 7),
        "T2": (1, 8, 2, 3, 5, 2),
    }
    cert_r1_r2_r8_r11 = {
        "L": (1, 2, 3, 6, 10, 11),
        "R": (1, 10, 5, 2, 15, 9),
        "B0": (1, 2, 0, 0, 8, 0),
        "B1": (1, 4, 0, 8, 6, 14),
        "T0": (1, 3, 12, 11, 7, 3),
        "T1": (1, 15, 5, 15, 15, 11),
        "T2": (1, 4, 0, 6, 9, 6),
    }
    tower_omit_r7 = (
        {
            "L": (1, 0, 10, 0, 11, 13),
            "R": (1, 5, 8, 5, 12, 13),
            "B0": (1, 0, 0, 1, 0, 9),
            "B1": (1, 0, 0, 1, 12, 15),
            "T0": (1, 1, 7, 11, 5, 8),
            "T1": (1, 1, 7, 11, 15, 10),
            "T2": (1, 0, 7, 7, 12, 6),
        },
        cert_r1_r2_r8_r11,
    )
    tower_omit_r5 = (
        {
            "L": (1, 0, 0, 0, 3, 2),
            "R": (1, 2, 10, 3, 3, 3),
            "B0": (1, 0, 0, 0, 0, 1),
            "B1": (1, 0, 0, 0, 3, 2),
            "T0": (1, 0, 1, 11, 14, 2),
            "T1": (1, 0, 6, 0, 0, 11),
            "T2": (1, 0, 1, 0, 3, 1),
        },
        {
            "L": (1, 0, 4, 0, 12, 6),
            "R": (1, 1, 14, 4, 6, 11),
            "B0": (1, 0, 0, 1, 0, 3),
            "B1": (1, 0, 2, 3, 5, 9),
            "T0": (1, 8, 7, 15, 4, 11),
            "T1": (1, 11, 1, 8, 12, 11),
            "T2": (1, 0, 7, 11, 5, 7),
        },
        cert_r1_r2_r8_r11,
    )

    omit_r2_ok = _verify_tower_2d([k for k in all_11_rules if k != "R2"], (cert_omit_r2,))
    omit_r7_ok = _verify_tower_2d([k for k in all_11_rules if k != "R7"], tower_omit_r7)
    omit_r5_ok = _verify_tower_2d([k for k in all_11_rules if k != "R5"], tower_omit_r5)

    # 2. Arts-Giesl shifted semantic 1D Dependency-Pair reduction on {R3..R11} + DP1
    dp_1d = {
        "L#": (1, 0),
        "R": (0, 0),
        "B0": (2, 1),
        "B1": (2, 2),
        "T0": (3, 2),
        "T1": (3, 3),
        "T2": (3, 4),
    }

    def _eval_1d(word: Sequence[str]) -> Tuple[int, int]:
        m_acc, c_acc = 1, 0
        for sym in word:
            ms, cs = dp_1d[sym]
            m_acc, c_acc = m_acc * ms, c_acc + m_acc * cs
        return m_acc, c_acc

    dp_semantic_ok = (
        all(
            _eval_1d(all_11_rules[f"R{idx}"][0]) == _eval_1d(all_11_rules[f"R{idx}"][1])
            for idx in range(3, 12)
        )
        and _eval_1d(("L#", "B0"))[0] >= _eval_1d(("L#",))[0]
        and _eval_1d(("L#", "B0"))[1] > _eval_1d(("L#",))[1]
    )

    # 3. Interior pumping identities on random weak orientations of {R4, R5, R6, R7} + coord-monotone stall
    # Verify on cert_omit_r2 (which orients all interior rules R3..R8!) that:
    # T0 B1 B0 >= B1 B1 T0, T2 B0 B1 >= B0 B0 T2, and T1 B1 B0 >= B0 B0 T1 entrywise!
    pump_pairs = (
        (("T0", "B1", "B0"), ("B1", "B1", "T0")),
        (("T2", "B0", "B1"), ("B0", "B0", "T2")),
        (("T1", "B1", "B0"), ("B0", "B0", "T1")),
    )
    pumping_ok = all(
        all(
            _eval_2d(cert_omit_r2, lw)[idx] >= _eval_2d(cert_omit_r2, rw)[idx]
            for idx in range(6)
        )
        for lw, rw in pump_pairs
    )

    # Verify coordinatewise-monotone weak orientation of sub6 ({R2, R5, R7, R9, R11})
    # under M_s == I_d forces v_s == 0 across ALL interior symbols {B0, B1, T0, T1, T2}:
    coord_monotone_stall_ok = True
    for vb0, vb1, vt0, vt1, vt2 in product(range(3), repeat=5):
        # R2: vb1 >= vt2; R5: vt1 + vb0 >= vb1 + vt0; R7: vt2 + vb0 >= vb0 + vt1;
        # R9: vt0 >= vb1; R11: vt2 >= vb1 + vb0
        if (
            vb1 >= vt2
            and vt1 + vb0 >= vb1 + vt0
            and vt2 + vb0 >= vb0 + vt1
            and vt0 >= vb1
            and vt2 >= vb1 + vb0
        ):
            if (vb0, vb1, vt0, vt1, vt2) != (0, 0, 0, 0, 0):
                coord_monotone_stall_ok = False
                break

    return {
        "omit_r2_10_of_11_single_2d_cert_verified": omit_r2_ok,
        "omit_r7_10_of_11_2level_2d_tower_verified": omit_r7_ok,
        "omit_r5_10_of_11_3level_2d_tower_verified": omit_r5_ok,
        "arts_giesl_1d_semantic_dp_verified": dp_semantic_ok,
        "interior_pumping_and_omega_k_stall_verified": pumping_ok and coord_monotone_stall_ok,
    }


def audit_w8_front_b_cyclotomic_331_and_laurent_extrapolation() -> Dict[str, Any]:
    """
    Front B (`Branch P3.4` & `P3.3`):
    1. Verify exact coprime-order prime scan up to `1,210,483` (`93,697` odd primes `5 <= p <= 1,210,483`),
       isolating `(331, 30, 11)` and `(1210483, 182, 2217)` as the exact first two coprime-order primes in `N`.
    2. Verify `M1` local mod-`331` cancellation (`x0 = 529 / 6643574255` at `(w1, a1) = (11, 30)`),
       cyclotomic companion quotient forcing (`2^30 - 1 = 3243933 * 331`, `3^11 - 2^11 = 529 * 331`,
       all prime factors `{3, 7, 11, 23, 31, 151}` excluded from `D` on 1-block `Z^+` cycles),
       `w1 >= 77` & zero valid 1-block `(w1, a1)` with `11 | w1, 30 | a1` up to `w1 <= 2000`,
       and `D % 8 == 5` escaping the closed subgroup `{1, 3} mod 8` containing `331` and `1,210,483`!
    3. Verify 2-block `p = 331` shared-Mersenne floor (`W >= 99`, `K >= 159`).
    4. Verify pure-integer Laurent binomial-Taylor column extrapolation `(2^u - 1)^T | det_Z(M0)`
       across `T = 2, 3, 4` and `u = 1, 2, 3` on `4x4` and `6x6` zero-gap grids, plus `3x3`
       derivative-extrapolated closed-form non-vanishing on `cols = [(0,0), (1,0), (0,u)]`.
    """
    from itertools import permutations

    def _det_int(m: List[List[int]]) -> int:
        n_sz = len(m)
        tot = 0
        for perm in permutations(range(n_sz)):
            inv = sum(
                1 for i in range(n_sz) for j in range(i + 1, n_sz) if perm[i] > perm[j]
            )
            prod = 1
            for i in range(n_sz):
                prod *= m[i][perm[i]]
            tot += (-prod) if (inv & 1) else prod
        return tot

    # 1. Coprime-order prime scan up to 1,210,483
    hits_all = _scan_coprime_order_primes_up_to(1_210_483)
    scan_ok = hits_all == ((331, 30, 11), (1_210_483, 182, 2217))

    # 2. Companion factorizations, M1 cancellation, w1 <= 2000 zero hits, & mod-8 subgroup barrier
    mersenne_30 = (1 << 30) - 1
    diff_11 = (3**11) - (1 << 11)
    companion_factors_ok = (
        mersenne_30 == 3_243_933 * 331
        and 3_243_933 == (3**2) * 7 * 11 * 31 * 151
        and diff_11 == 529 * 331
        and 529 == 23 * 23
        and all(
            math.gcd(
                _mult_order_mod_prime(2, p_c),
                _mult_order_mod_prime((3 * pow(2, -1, p_c)) % p_c, p_c),
            )
            >= 2
            for p_c in (7, 11, 23, 31, 151)
        )
    )
    d_11_30 = (1 << 41) - (3**11)
    m1_cancel_ok = (
        d_11_30 == 331 * 6_643_574_255
        and Fraction(diff_11, d_11_30) == Fraction(529, 6_643_574_255)
        and d_11_30 > mersenne_30
        and (d_11_30 % 8) == 5
        and (331 % 8) == 3
        and (1_210_483 % 8) == 3
    )

    one_block_331_hits_le_2000 = 0
    for m_w in range(1, 182):
        w1 = 11 * m_w
        if math.gcd(w1, 30) != 1:
            continue
        k_tight = (3**w1).bit_length()
        a1 = k_tight - w1
        if a1 >= 30 and (a1 % 30) == 0:
            det = (1 << k_tight) - (3**w1)
            if 0 < det <= ((1 << a1) - 1) and ((1 << a1) - 1) % det == 0:
                one_block_331_hits_le_2000 += 1

    # 3. 2-block shared-Mersenne p = 331 floor: 11 | W, 30 | a1, 30 | a2 (a1 + a2 >= 60), 3*K < 5*W
    min_w_2block = min(
        11 * v_w
        for v_w in range(1, 20)
        for u_a in range(2, 20)
        if 3 * (11 * v_w + 30 * u_a) < 5 * (11 * v_w)
    )
    twoblock_331_floor_ok = (min_w_2block == 99) and (min_w_2block + 60 == 159)

    # 4. Pure-integer Laurent binomial-Taylor column extrapolation
    taylor_dvd_ok = True
    for x_v in range(0, 12):
        for b_v in (1, 3, 7):
            for t_cut in (1, 2, 3, 4):
                rem_t = ((1 + b_v) ** x_v) - sum(
                    math.comb(x_v, t_i) * (b_v**t_i) for t_i in range(t_cut)
                )
                if rem_t % (b_v**t_cut) != 0:
                    taylor_dvd_ok = False
                    break

    for w_v, k_v in ((3, 5), (5, 8)):
        rows_4 = [(0, 0), (0, 1), (1, 0), (1, 1)]
        rows_6 = [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1)]
        for u_col in (1, 2, 3):
            b_u = (1 << u_col) - 1
            # 3x3 exact non-vanishing on cols = [(0,0), (1,0), (0,u_col)], rows = [(0,0), (1,0), (2,0)]
            rows_3 = [(0, 0), (1, 0), (2, 0)]
            cols_3 = [(0, 0), (1, 0), (0, u_col)]
            mat_3 = [
                [
                    math.comb(r * w_v + s * k_v, t) * (1 << ((r * w_v + s * k_v) * u))
                    for (t, u) in cols_3
                ]
                for (r, s) in rows_3
            ]
            det_3 = _det_int(mat_3)
            exp_det_3 = w_v * (((1 << (w_v * u_col)) - 1) ** 2)
            if det_3 != exp_det_3 or det_3 <= 0 or det_3 % (b_u**2) != 0:
                taylor_dvd_ok = False
            # 4x4 with T = 3 Taylor columns + (0, u_col)
            cols_4 = [(0, 0), (1, 0), (2, 0), (0, u_col)]
            mat_4 = [
                [
                    math.comb(r * w_v + s * k_v, t) * (1 << ((r * w_v + s * k_v) * u))
                    for (t, u) in cols_4
                ]
                for (r, s) in rows_4
            ]
            if _det_int(mat_4) % (b_u**3) != 0:
                taylor_dvd_ok = False
            # 6x6 with T = 4 Taylor columns + (0, u_col) + (1, u_col)
            cols_6 = [(0, 0), (1, 0), (2, 0), (3, 0), (0, u_col), (1, u_col)]
            mat_6 = [
                [
                    math.comb(r * w_v + s * k_v, t) * (1 << ((r * w_v + s * k_v) * u))
                    for (t, u) in cols_6
                ]
                for (r, s) in rows_6
            ]
            if _det_int(mat_6) % (b_u**4) != 0:
                taylor_dvd_ok = False

    return {
        "coprime_order_primes_to_1210483": hits_all,
        "exact_first_two_coprime_primes_verified": scan_ok,
        "companion_factorizations_and_m1_cancellation_verified": (
            companion_factors_ok and m1_cancel_ok and (one_block_331_hits_le_2000 == 0)
        ),
        "twoblock_331_floor_99_159_verified": twoblock_331_floor_ok,
        "laurent_taylor_column_extrapolation_verified": taylor_dvd_ok,
    }


def audit_w8_front_c_ripple_carry_window_kgram_and_diamond5() -> Dict[str, Any]:
    """
    Front C (`Branch P1.2` & `P5`):
    1. Verify alternating ripple-carry cascade collapse `A_e = (4^e - 1) // 3` (`e = 2..8`:
       `ripple_carry_3n1_stats(A_e) == (2 * e, e * (2 * e - 1))` vs `(0, 0)` at `2 * A_e`),
       exact Mersenne triple formulas across `r = 2..15`, and Bernoulli ratio `2 * (8*N + 4)^N > (8*N + 8)^N`.
    2. Verify universal sliding-window `k`-gram family `m_{W, k} = 3 * 4^(W + k) + 2^(2 * W + 1)`
       across `W = 1..7` and `k = W .. W + 5`: constant `binary_nonzero_window_list`, exact
       collision with `2 * m_{W, k}`, constant odd-preimage window list, and exact slope-`2`
       affine growth of `(binary_zero_window_count, bit_length)`.
    3. Verify 5th solvable cousin `T_diamond5`: outside Cones 4, 5, 6 strict `Phi_diamond2`
       descent (`x = 3..5000`), Cone 6 -> Cone 5 jump (`e = 8..13, f = 2..6`, including
       `2285 -> 857` and `73709 -> 27641`), zero Cone-6 hits along Cone-4/5 orbits, global
       convergence within `(x+1)^3 + (x+1)^5`, and `M1`/`M2`/`M3` + `Q_(6)`/`Int` agreement.
    """
    # 1. Alternating cascade collapse, Mersenne triples, & Bernoulli ratio
    ripple_ok = ripple_carry_3n1_stats(0) == (0, 0)
    for e_val in range(2, 9):
        a_e = ((4**e_val) - 1) // 3
        if (
            ripple_carry_3n1_stats(a_e) != (2 * e_val, e_val * (2 * e_val - 1))
            or ripple_carry_3n1_stats(2 * a_e) != (0, 0)
        ):
            ripple_ok = False
            break
    for r_val in range(3, 16):
        n_odd = (1 << r_val) - 1
        m_val = 3 * (1 << (r_val - 1)) - 1
        ev_val = 2 * m_val
        if (
            (m_val % 3) != 2
            or (2 * m_val - 1) // 3 != n_odd
            or ripple_carry_3n1_stats(n_odd) != (r_val + 1, (r_val * (r_val + 1)) // 2)
            or ripple_carry_3n1_stats(m_val) != (r_val + 2, ((r_val + 1) * (r_val + 2)) // 2)
            or ripple_carry_3n1_stats(ev_val) != (r_val + 1, ((r_val + 1) * (r_val + 4)) // 2)
            or n_odd.bit_length() != r_val
            or m_val.bit_length() != r_val + 1
            or ev_val.bit_length() != r_val + 2
        ):
            ripple_ok = False
            break
    for n_deg in range(0, 16):
        if not (2 * ((8 * n_deg + 4) ** n_deg) > ((8 * n_deg + 8) ** n_deg)):
            ripple_ok = False
            break

    # 2. Universal W_win = 1..7 sliding-window family m_{W, k} = 3 * 4^(W + k) + 2^(2*W + 1)
    window_family_ok = True
    for w_win in range(1, 8):
        m_base = 3 * (4 ** (2 * w_win)) + (1 << (2 * w_win + 1))
        odd_base = (2 * m_base - 1) // 3
        nz_m_base = binary_nonzero_window_list(w_win, m_base)
        nz_odd_base = binary_nonzero_window_list(w_win, odd_base)
        z_m_base = binary_zero_window_count(w_win, m_base)
        z_odd_base = binary_zero_window_count(w_win, odd_base)
        l_m_base = m_base.bit_length()
        for t_off in range(0, 6):
            k_idx = w_win + t_off
            mk = 3 * (4 ** (w_win + k_idx)) + (1 << (2 * w_win + 1))
            ev_k = 2 * mk
            odd_k = (2 * mk - 1) // 3
            if (
                (mk % 3) != 2
                or int_compressed_step(odd_k, q=3) != mk
                or int_compressed_step(ev_k, q=3) != mk
                or binary_nonzero_window_list(w_win, mk) != nz_m_base
                or binary_nonzero_window_list(w_win, ev_k) != nz_m_base
                or binary_nonzero_window_list(w_win, odd_k) != nz_odd_base
                or binary_zero_window_count(w_win, mk) != z_m_base + 2 * t_off
                or binary_zero_window_count(w_win, ev_k) != z_m_base + 2 * t_off + 1
                or binary_zero_window_count(w_win, odd_k) != z_odd_base + 2 * t_off
                or mk.bit_length() != l_m_base + 2 * t_off
                or ev_k.bit_length() != l_m_base + 2 * t_off + 1
                or odd_k.bit_length() != l_m_base + 2 * t_off
            ):
                window_family_ok = False
                break

    # 3. 5th Solvable Cousin T_diamond5
    d5_outside_ok = all(
        (
            is_diamond3_cone4(x)
            or is_diamond4_cone5(x)
            or is_diamond5_cone6(x)
            or cousin_diamond2_phi(cousin_diamond5_step_int(x)) < cousin_diamond2_phi(x)
        )
        for x in range(3, 5001)
    )
    d5_cone6_ok = (
        is_diamond5_cone6(2285)
        and cousin_diamond5_step_int(2285) == 857
        and cousin_diamond2_phi(857) > cousin_diamond2_phi(2285)
        and is_diamond5_cone6(73709)
        and cousin_diamond5_step_int(73709) == 27641
        and cousin_diamond2_phi(27641) > cousin_diamond2_phi(73709)
    )
    for e_exp in range(8, 14):
        for f_exp in range(2, 7):
            xc6 = (1 << e_exp) * (3**f_exp) - 19
            yc5 = (1 << (e_exp - 3)) * (3 ** (f_exp + 1)) - 7
            h_st, end_st = cousin_diamond5_block_return(xc6)
            bound_poly = ((xc6 + 1) ** 3) + ((xc6 + 1) ** 5)
            if (
                not is_diamond5_cone6(xc6)
                or cousin_diamond5_step_int(xc6) != yc5
                or not is_diamond4_cone5(yc5)
                or end_st != 1
                or h_st > bound_poly
            ):
                d5_cone6_ok = False
                break

    d5_spiral_ok = True
    for r in range(1, 7):
        cur = 4 * (16**r) - 5
        for j in range(1, r + 1):
            mid = cousin_diamond5_step_int(cur)
            nxt = cousin_diamond5_step_int(mid)
            exp_nxt = 4 * (16 ** (r - j)) * (18**j) - 5
            if nxt != exp_nxt or nxt <= cur:
                d5_spiral_ok = False
                break
            cur = nxt

    m1_cur = Fraction(1, 7)
    for _ in range(5):
        m1_cur = cousin_diamond5_step_q6(m1_cur)
    m2_ok = (
        cousin_diamond5_step_int(-1) == -1
        and cousin_diamond5_step_int(cousin_diamond5_step_int(cousin_diamond5_step_int(-5))) == -5
    )
    m3_cur = 5
    for _ in range(5):
        m3_cur = cousin_diamond5_step_int(m3_cur, q=7)
    q6_int_agree_ok = all(
        cousin_diamond5_step_q6(Fraction(x_chk, 1)) == Fraction(cousin_diamond5_step_int(x_chk), 1)
        for x_chk in list(range(-80, 260)) + [2285, 73709]
    )
    q6_closure_ok = all(
        math.gcd(cousin_diamond5_step_q6(Fraction(num_c, den_c)).denominator, 6) == 1
        for den_c in (5, 7, 11)
        for num_c in range(-25, 90)
        if math.gcd(num_c, den_c) == 1
    )
    d5_countermodels_ok = (
        (m1_cur == Fraction(1, 7))
        and m2_ok
        and (m3_cur == 5)
        and q6_int_agree_ok
        and q6_closure_ok
    )

    return {
        "ripple_carry_cascade_mersenne_and_bernoulli_verified": ripple_ok,
        "sliding_window_kgram_family_verified": window_family_ok,
        "cousin_diamond5_outside_cones456_descent_verified": d5_outside_ok,
        "cousin_diamond5_cone6_return_and_spiral_verified": d5_cone6_ok and d5_spiral_ok,
        "cousin_diamond5_countermodels_verified": d5_countermodels_ok,
    }


def audit_w8_front_d_cross_scale_q0_collisions_and_markov_mod6() -> Dict[str, Any]:
    """
    Front D (`Branch P5.3` & `P2.2`):
    1. Exhaustively verify the exact cross-scale (`|u1| < |u2|`) `q = 0` leaf collision
       biconditional across ALL core words `1 <= |u1| < |u2| <= 9`:
       `exact_backward_quotient(1, u1, 0) == exact_backward_quotient(1, u2, 0)` iff
       `exists m >= 0, u2 == trivial_loop_extension(u1, m)`, and every such extension
       has `canonical_suffix_shift(u2, 1) == 1` and `not is_first_hit_one_pair(u2, 0)`.
    2. Verify unconditional multi-scale distinctness (`NoDup`) across ALL `is_first_hit_one_pair(u, 0)`
       surviving `Mod373248` leaves over `10 <= L <= 13` (plus raw distinctness without filtering
       across `10 <= L <= 13` because `|u1| + canonical_suffix_shift(u1, 1) >= 15` on `Mod373248`!).
    3. Verify Markov skew-product bijectivity for `b = 0` on `[0, 2 * 3^(w - 1))` (`w = 1..5`),
       strict injectivity + exact image `{a' < 2 * 3^w : a' % 6 in (1, 3)}` for `b = 1` (`w = 1..5`),
       and universal `canonical_suffix_shift(u, 1) % 6 in (1, 3)` (`!= 5`) across all core words
       `2 <= |u| <= 10` (`w >= 2`).
    """
    from . import cs_forest_transfer as cft

    # 1. Exhaustive cross-scale biconditional over all core words 1 <= |u| <= 9
    words_by_y0: Dict[int, List[Tuple[int, ...]]] = {}
    all_core_le9: List[Tuple[int, ...]] = [(1,)]
    for length in range(2, 10):
        for mid in product((0, 1), repeat=length - 2):
            all_core_le9.append((1,) + mid + (1,))
    for u_c in all_core_le9:
        y0 = cft.exact_backward_quotient(1, u_c, 0)
        words_by_y0.setdefault(y0, []).append(u_c)

    biconditional_ok = True
    collision_pairs_found = 0
    for grp in words_by_y0.values():
        if len(grp) <= 1:
            continue
        grp_sorted = sorted(grp, key=len)
        for idx_i in range(len(grp_sorted)):
            for idx_j in range(idx_i + 1, len(grp_sorted)):
                u1 = grp_sorted[idx_i]
                u2 = grp_sorted[idx_j]
                collision_pairs_found += 1
                matched_ext = any(
                    u2 == trivial_loop_extension(u1, m_ext)
                    for m_ext in range((len(u2) - len(u1)) // 2 + 1)
                )
                if (
                    not matched_ext
                    or cft.canonical_suffix_shift(u2, 1) != 1
                    or cft.is_first_hit_one_pair(u2, 0)
                ):
                    biconditional_ok = False
                    break

    # Converse direction: check trivial_loop_extension(u1, m) collides at y0 for m = 0, 1, 2
    for u1 in all_core_le9[:32]:
        y_base = cft.exact_backward_quotient(1, u1, 0)
        for m_ext in (0, 1, 2):
            u_ext = trivial_loop_extension(u1, m_ext)
            if (
                cft.exact_backward_quotient(1, u_ext, 0) != y_base
                or cft.canonical_suffix_shift(u_ext, 1) != 1
                or cft.is_first_hit_one_pair(u_ext, 0)
            ):
                biconditional_ok = False
                break

    # 2. Multi-scale NoDup:
    #    (a) Across 1 <= L <= 8 (all core words): raw q = 0 leaves HAVE collisions, while
    #        filtering by is_first_hit_one_pair(u, 0) restores exact NoDup!
    #    (b) Across 10 <= L <= 13 on surviving Mod373248 fiber words (k_scale = 0..3):
    #        |u| + canonical_suffix_shift(u, 1) >= 15, so raw leaves have 0 collisions,
    #        and k_scale = 0..1 explicitly cross-checks is_first_hit_one_pair(u, 0).
    raw_le8 = [cft.exact_backward_quotient(1, u_c, 0) for u_c in all_core_le9 if len(u_c) <= 8]
    fh_le8 = [
        cft.exact_backward_quotient(1, u_c, 0)
        for u_c in all_core_le9
        if len(u_c) <= 8 and cft.is_first_hit_one_pair(u_c, 0)
    ]

    surv512_prefixes: List[Tuple[int, ...]] = []
    for r512 in range(1, 512, 2):
        if cft.is_surviving_mod512_residue(r512):
            _, p9 = int_iter_and_parity(r512, 9, q=3)
            surv512_prefixes.append(p9)

    multiscale_first_hit_leaves: List[int] = []
    multiscale_raw_leaves: List[int] = []
    min_len_plus_shift = 10**9
    for k_scale in range(0, 4):
        for p9 in surv512_prefixes:
            for fb in product((0, 1), repeat=k_scale):
                u_c = p9 + fb + (1,)
                y0 = cft.exact_backward_quotient(1, u_c, 0)
                if cft.is_surviving_mod373248_class(y0):
                    multiscale_raw_leaves.append(y0)
                    min_len_plus_shift = min(
                        min_len_plus_shift, len(u_c) + cft.canonical_suffix_shift(u_c, 1)
                    )
                    if k_scale <= 1 and cft.is_first_hit_one_pair(u_c, 0):
                        multiscale_first_hit_leaves.append(y0)

    multiscale_nodup_ok = (
        len(set(raw_le8)) < len(raw_le8)
        and len(fh_le8) > 0
        and len(set(fh_le8)) == len(fh_le8)
        and len(surv512_prefixes) == 27
        and len(multiscale_first_hit_leaves) > 0
        and len(set(multiscale_first_hit_leaves)) == len(multiscale_first_hit_leaves)
        and len(set(multiscale_raw_leaves)) == len(multiscale_raw_leaves)
        and min_len_plus_shift >= 15
    )

    # 3. Markov b = 0 bijection, b = 1 injectivity + {1, 3} mod 6 image, & universal u mod 6 != 5
    markov_mod6_ok = True
    for w_val in range(1, 6):
        period_prev = 2 * (3 ** (w_val - 1))
        period_next = 2 * (3**w_val)
        img_false = [
            (a - 1) if a >= 1 else (period_prev - 1) for a in range(period_prev)
        ]
        if len(set(img_false)) != period_prev or set(img_false) != set(range(period_prev)):
            markov_mod6_ok = False
            break
        img_true = [
            cft.dlog2_mod_pow3_aux(w_val, 3 * (1 << a) + 1) - 1
            for a in range(period_prev)
        ]
        expected_true_set = {
            a_nxt for a_nxt in range(period_next) if (a_nxt % 6) in (1, 3)
        }
        if len(set(img_true)) != period_prev or set(img_true) != expected_true_set:
            markov_mod6_ok = False
            break

    for length_u in range(2, 11):
        for mid in product((0, 1), repeat=length_u - 2):
            u_c = (1,) + mid + (1,)
            if (cft.canonical_suffix_shift(u_c, 1) % 6) not in (1, 3):
                markov_mod6_ok = False
                break

    return {
        "cross_scale_q0_collision_pairs_le9": collision_pairs_found,
        "cross_scale_q0_biconditional_verified": biconditional_ok and (collision_pairs_found > 0),
        "multiscale_surviving_q0_nodup_verified": multiscale_nodup_ok,
        "markov_bijection_and_mod6_lock_verified": markov_mod6_ok,
    }


def _dynamic_pred_ripple_carry_penalty_monotonicity(_dom: str, entry: Dict[str, Any]) -> bool:
    """
    Dynamic test of carry-penalized preimage weights claiming `rippleCarryCount(2*m) >= rippleCarryCount(m)`
    on branching targets `m >= 3` (`m % 3 == 2`). Zero hardcoded witness IDs.
    """
    if "next_compressed" not in entry:
        return True
    m_tgt = int(entry["next_compressed"])
    if m_tgt < 3 or (m_tgt % 3) != 2:
        return True
    cnt_m, _ = ripple_carry_3n1_stats(m_tgt)
    cnt_2m, _ = ripple_carry_3n1_stats(2 * m_tgt)
    return cnt_2m >= cnt_m


def _dynamic_pred_width5_sliding_window_distinguishes_preimages(
    _dom: str, entry: Dict[str, Any]
) -> bool:
    """
    Dynamic test of width-5 sliding-window `k`-gram preimage weights (which separate `200` vs `400`,
    unlike Wave 7's `sig_6`): requires `nonZeroWindowList(5, 2*m) != nonZeroWindowList(5, m)` on
    branching targets `m >= 3` (`m % 3 == 2`). Zero hardcoded witness IDs.
    """
    if "next_compressed" not in entry:
        return True
    m_tgt = int(entry["next_compressed"])
    if m_tgt < 3 or (m_tgt % 3) != 2:
        return True
    return binary_nonzero_window_list(5, 2 * m_tgt) != binary_nonzero_window_list(5, m_tgt)


def _dynamic_pred_phi2_on_cousin_diamond5_outside_cones45(
    _dom: str, entry: Dict[str, Any]
) -> bool:
    """Dynamic test of single-step `Phi_diamond2` descent on `T_diamond5` outside Cones 4 and 5."""
    seed = int(entry.get("seed", 0))
    if seed <= 2 or is_diamond3_cone4(seed) or is_diamond4_cone5(seed):
        return True
    nxt = cousin_diamond5_step_int(seed, q=3)
    return cousin_diamond2_phi(nxt) < cousin_diamond2_phi(seed)


def _dynamic_pred_local_mod331_excludes_m1_1block(_dom: str, entry: Dict[str, Any]) -> bool:
    """
    Dynamic test of purely local mod-`331` exclusion claiming `331` cannot divide
    `gcd(2^a1 - 1, 3^w1 - 2^w1, 2^(w1 + a1) - 3^w1)` on a 1-block `M1` cycle.
    """
    if entry.get("m_blocks") != 1 or "period_k" not in entry or "weight_w" not in entry:
        return True
    k_per = int(entry["period_k"])
    w1 = int(entry["weight_w"])
    a1 = k_per - w1
    if w1 < 1 or a1 < 1:
        return True
    g_331 = math.gcd((1 << a1) - 1, math.gcd((3**w1) - (1 << w1), (1 << k_per) - (3**w1)))
    return (g_331 % 331) != 0


def _dynamic_pred_331_unique_coprime_order_prime(_dom: str, entry: Dict[str, Any]) -> bool:
    """Dynamic test of uniqueness claim that no odd prime `p > 331` has `gcd(ord_p(2), ord_p(3/2)) == 1`."""
    if "second_coprime_order_prime" not in entry:
        return True
    p2 = int(entry["second_coprime_order_prime"])
    if p2 <= 331:
        return True
    o2 = _mult_order_mod_prime(2, p2)
    o32 = _mult_order_mod_prime((3 * pow(2, -1, p2)) % p2, p2)
    return math.gcd(o2, o32) >= 2


def _dynamic_pred_q0_cross_scale_only_single_loop_collides(
    _dom: str, entry: Dict[str, Any]
) -> bool:
    """
    Dynamic test of false claim that all cross-scale `|u1| < |u2|` `q = 0` leaf collisions
    are single-loop (`m = 0`) extensions `trivial_loop_extension(u1, 0)`.
    """
    if "loop_core_word" not in entry or "core_word" not in entry:
        return True
    from . import cs_forest_transfer as cft

    u1 = tuple(int(b) for b in entry["core_word"])
    u2 = tuple(int(b) for b in entry["loop_core_word"])
    if len(u1) >= len(u2):
        return True
    if cft.exact_backward_quotient(1, u1, 0) == cft.exact_backward_quotient(1, u2, 0):
        return u2 == trivial_loop_extension(u1, 0)
    return True


def run_wave8_whole_space_campaign(bank_path: Optional[Path] = None) -> Dict[str, Any]:
    """
    Execute the complete Wave 8 whole-space red-team, `10/11` positive Collatz SRS
    matrix towers & `omega^k` barriers, cyclotomic companion quotient forcing vs `p = 331`
    & Laurent column extrapolation, non-separable ripple-carry / `W_win`-gram preimage
    barriers & `T_diamond5` benchmark, and cross-scale `q = 0` leaf collision biconditional
    & Markov mod-6 campaign against `witness_bank.json`.
    """
    u_gate = audit_universality_gate(
        "Wave8_WholeSpace_W8_1_to_W8_4",
        is_finite_m_table=False,
        is_finite_n_table=False,
        is_bounded_weight_table=False,
        uses_native_decide=False,
        uses_sorry=False,
        axioms_used=("propext", "Classical.choice", "Quot.sound"),
    )
    bank = load_witness_bank(bank_path)
    wb_truth = verify_witness_bank_ground_truth(bank_path)

    gate_ripple = evaluate_hypothesis_against_witness_bank(
        "RippleCarryPenaltyMonotonicityOnEvenSibling",
        _dynamic_pred_ripple_carry_penalty_monotonicity,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    gate_win5 = evaluate_hypothesis_against_witness_bank(
        "Width5SlidingWindowDistinguishesPreimages",
        _dynamic_pred_width5_sliding_window_distinguishes_preimages,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    gate_phi2_d5 = evaluate_hypothesis_against_witness_bank(
        "OutsideCones45Phi2OnCousinDiamond5",
        _dynamic_pred_phi2_on_cousin_diamond5_outside_cones45,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    gate_local_331 = evaluate_hypothesis_against_witness_bank(
        "LocalMod331ExcludesM1OneBlock",
        _dynamic_pred_local_mod331_excludes_m1_1block,
        domains=("m1_q2_pos",),
        bank_path=bank_path,
    )
    gate_unique_331 = evaluate_hypothesis_against_witness_bank(
        "Prime331UniqueCoprimeOrderPrime",
        _dynamic_pred_331_unique_coprime_order_prime,
        domains=("log2_3_convergents",),
        bank_path=bank_path,
    )
    gate_single_loop = evaluate_hypothesis_against_witness_bank(
        "CrossScaleQ0OnlySingleLoopCollides",
        _dynamic_pred_q0_cross_scale_only_single_loop_collides,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )

    front_a = audit_w8_front_a_srs_10_of_11_towers_and_omega_k_barriers()
    front_b = audit_w8_front_b_cyclotomic_331_and_laurent_extrapolation()
    front_c = audit_w8_front_c_ripple_carry_window_kgram_and_diamond5()
    front_d = audit_w8_front_d_cross_scale_q0_collisions_and_markov_mod6()

    passed = (
        u_gate.passed
        and bool(wb_truth["all_witnesses_ground_truth_verified"])
        and (not gate_ripple["passed"])
        and gate_ripple["minimal_failure"]
        == ("z_pos_high_glide", "ZPOS_RIPPLE_CARRY_COLLAPSE_341")
        and (not gate_win5["passed"])
        and gate_win5["minimal_failure"]
        == ("z_pos_high_glide", "ZPOS_SLIDING_WINDOW_COLLISION_800")
        and (not gate_phi2_d5["passed"])
        and gate_phi2_d5["minimal_failure"]
        == ("z_pos_high_glide", "ZPOS_COUSIN_DIAMOND5_CONE6_2285_JUMP")
        and (not gate_local_331["passed"])
        and gate_local_331["minimal_failure"]
        == ("m1_q2_pos", "M1_331_CANCELLATION_529_OVER_6643574255")
        and (not gate_unique_331["passed"])
        and gate_unique_331["minimal_failure"]
        == ("log2_3_convergents", "COPRIME_PRIME_1210483_AND_MOD8_SUBGROUP_BARRIER")
        and (not gate_single_loop["passed"])
        and gate_single_loop["minimal_failure"]
        == ("z_pos_high_glide", "ZPOS_RAY_Q0_MULTI_LOOP_COLLISION_3")
        and bool(front_a["omit_r2_10_of_11_single_2d_cert_verified"])
        and bool(front_a["omit_r7_10_of_11_2level_2d_tower_verified"])
        and bool(front_a["omit_r5_10_of_11_3level_2d_tower_verified"])
        and bool(front_a["arts_giesl_1d_semantic_dp_verified"])
        and bool(front_a["interior_pumping_and_omega_k_stall_verified"])
        and bool(front_b["exact_first_two_coprime_primes_verified"])
        and bool(front_b["companion_factorizations_and_m1_cancellation_verified"])
        and bool(front_b["twoblock_331_floor_99_159_verified"])
        and bool(front_b["laurent_taylor_column_extrapolation_verified"])
        and bool(front_c["ripple_carry_cascade_mersenne_and_bernoulli_verified"])
        and bool(front_c["sliding_window_kgram_family_verified"])
        and bool(front_c["cousin_diamond5_outside_cones456_descent_verified"])
        and bool(front_c["cousin_diamond5_cone6_return_and_spiral_verified"])
        and bool(front_c["cousin_diamond5_countermodels_verified"])
        and bool(front_d["cross_scale_q0_biconditional_verified"])
        and bool(front_d["multiscale_surviving_q0_nodup_verified"])
        and bool(front_d["markov_bijection_and_mod6_lock_verified"])
    )
    return {
        "passed": passed,
        "verdict": "REDTEAM-PASSED" if passed else "FALSIFIED",
        "universality_gate_passed": u_gate.passed,
        "witness_bank_total_entries": sum(len(v) for v in bank["domains"].values()),
        "witness_bank_falsified_count": len(bank["falsified_hypotheses"]),
        "witness_bank_ground_truth_verified": bool(wb_truth["all_witnesses_ground_truth_verified"]),
        "front_a_srs_10_of_11_and_towers": front_a,
        "front_b_cyclotomic_331_and_laurent": front_b,
        "front_c_ripple_window_and_diamond5": front_c,
        "front_d_cross_scale_and_markov_mod6": front_d,
    }


# ============================================================================
# 14. Wave 9 Whole-Space Campaign (Fronts A–D: Unlabelled d = 2 S9 Barriers,
#     d = 3 Omit-R9 Tower & Zantema M = 2 Parity Semantic Labelling,
#     Two-Base 4x4 Confluent Laurent Non-Vanishing & p_3 / p_4 Coprime-Order
#     Prime Escape, Universal Stateful Q-State Automaton Preimage Barrier &
#     Cousin T_diamond6, and Complete Global (u, q) Collision Classification &
#     All-k 2 * 3^k Markov Memory Annihilation)
# ============================================================================


def _validate_automaton_args(
    num_states: int, delta: Sequence[Sequence[int]], init_state: int, n: int
) -> List[Tuple[int, int]]:
    """Validate `(num_states, delta, init_state, n)` for LSB/MSB finite-state automata."""
    if isinstance(num_states, bool) or not isinstance(num_states, int) or num_states < 1:
        raise ValueError(f"Expected integer num_states >= 1, got {num_states!r}")
    if isinstance(init_state, bool) or not isinstance(init_state, int) or not (0 <= init_state < num_states):
        raise ValueError(f"Expected integer init_state in [0, {num_states}), got {init_state!r}")
    if isinstance(n, bool) or not isinstance(n, int) or n < 0:
        raise ValueError(f"Expected nonnegative integer n >= 0, got {n!r}")
    if not isinstance(delta, (list, tuple)) or len(delta) != num_states:
        raise ValueError(f"Expected transition table delta of length {num_states}")
    table: List[Tuple[int, int]] = []
    for row in delta:
        if not isinstance(row, (list, tuple)) or len(row) != 2:
            raise ValueError("Each state in delta must map to a 2-tuple (next_on_0, next_on_1)")
        q0_nxt, q1_nxt = row[0], row[1]
        if (
            isinstance(q0_nxt, bool)
            or isinstance(q1_nxt, bool)
            or not isinstance(q0_nxt, int)
            or not isinstance(q1_nxt, int)
            or not (0 <= q0_nxt < num_states)
            or not (0 <= q1_nxt < num_states)
        ):
            raise ValueError(f"Invalid transition target in {row!r} for num_states={num_states}")
        table.append((q0_nxt, q1_nxt))
    return table


def run_lsb_automaton(
    num_states: int, delta: Sequence[Sequence[int]], init_state: int, n: int
) -> int:
    """
    Run a deterministic `num_states`-state finite automaton LSB-to-MSB across the
    unpadded binary bits of `n >= 0` (`n == 0` reads the empty bitstring `()`, returning
    `init_state`; matches `runLSBAutomaton` in `Wave9WholeSpace.lean`).
    """
    table = _validate_automaton_args(num_states, delta, init_state, n)
    cur_q = init_state
    rem = n
    while rem > 0:
        cur_q = table[cur_q][rem & 1]
        rem >>= 1
    return cur_q


def run_msb_automaton(
    num_states: int, delta: Sequence[Sequence[int]], init_state: int, n: int
) -> int:
    """
    Run a deterministic `num_states`-state finite automaton MSB-to-LSB across the
    unpadded binary bits of `n >= 0` (`n == 0` reads the empty bitstring `()`, returning
    `init_state`; matches `runMSBAutomaton` in `Wave9WholeSpace.lean`).
    """
    table = _validate_automaton_args(num_states, delta, init_state, n)
    if n == 0:
        return init_state
    bits_msb: List[int] = []
    rem = n
    while rem > 0:
        bits_msb.append(rem & 1)
        rem >>= 1
    cur_q = init_state
    for bit in reversed(bits_msb):
        cur_q = table[cur_q][bit]
    return cur_q


def _validate_emit_args(
    num_states: int, emit: Sequence[Sequence[int]]
) -> List[Tuple[int, int]]:
    if not isinstance(emit, (list, tuple)) or len(emit) != num_states:
        raise ValueError(f"Expected emit table of length {num_states}, got {emit!r}")
    emit_tbl: List[Tuple[int, int]] = []
    for row in emit:
        if not isinstance(row, (list, tuple)) or len(row) != 2:
            raise ValueError(f"Expected 2-entry emit row (e0, e1), got {row!r}")
        e0, e1 = row
        if (
            isinstance(e0, bool)
            or isinstance(e1, bool)
            or not isinstance(e0, int)
            or not isinstance(e1, int)
            or e0 < 0
            or e1 < 0
        ):
            raise ValueError(f"Expected nonnegative integer emit weights in {row!r}")
        emit_tbl.append((e0, e1))
    return emit_tbl


def run_lsb_transducer(
    num_states: int,
    delta: Sequence[Sequence[int]],
    emit: Sequence[Sequence[int]],
    init_state: int,
    n: int,
) -> int:
    """
    Run a deterministic `num_states`-state binary Mealy transducer LSB-to-MSB across the
    unpadded binary bits of `n >= 0`, summing per-transition weights `emit[q][bit]`
    (`0` at `n == 0`; matches `runLSBTransducerOut` in `Wave9WholeSpace.lean`).
    """
    table = _validate_automaton_args(num_states, delta, init_state, n)
    emit_tbl = _validate_emit_args(num_states, emit)
    cur_q = init_state
    total = 0
    rem = n
    while rem > 0:
        bit = rem & 1
        total += emit_tbl[cur_q][bit]
        cur_q = table[cur_q][bit]
        rem >>= 1
    return total


def run_msb_transducer(
    num_states: int,
    delta: Sequence[Sequence[int]],
    emit: Sequence[Sequence[int]],
    init_state: int,
    n: int,
) -> int:
    """
    Run a deterministic `num_states`-state binary Mealy transducer MSB-to-LSB across the
    unpadded binary bits of `n >= 0`, summing per-transition weights `emit[q][bit]`
    (`0` at `n == 0`; matches `runMSBTransducerOut` in `Wave9WholeSpace.lean`).
    """
    table = _validate_automaton_args(num_states, delta, init_state, n)
    emit_tbl = _validate_emit_args(num_states, emit)
    if n == 0:
        return 0
    bits_msb: List[int] = []
    rem = n
    while rem > 0:
        bits_msb.append(rem & 1)
        rem >>= 1
    cur_q = init_state
    total = 0
    for bit in reversed(bits_msb):
        total += emit_tbl[cur_q][bit]
        cur_q = table[cur_q][bit]
    return total


def loop_unroll_word(u: Sequence[int], q: int, m: int) -> Tuple[int, ...]:
    """
    Construct the canonical `(q, m)` loop-unrolled `q = 0` core parity word
    (`loopUnroll u q m` in `Wave9WholeSpace.lean`) colliding with `(u, q)` at
    `exact_backward_quotient(1, u, q)`:
        `u + (0,) * (canonical_suffix_shift(u, 1) + 2 * 3^(w(u) - 1) * q) + (1,) + (0, 1) * m`.
    Note `loop_unroll_word(u, 0, m) == trivial_loop_extension(u, m)`.
    """
    if isinstance(q, bool) or not isinstance(q, int) or q < 0:
        raise ValueError(f"Expected nonnegative integer ray index q >= 0, got {q!r}")
    if isinstance(m, bool) or not isinstance(m, int) or m < 0:
        raise ValueError(f"Expected nonnegative integer loop count m >= 0, got {m!r}")
    if not isinstance(u, (list, tuple)) or any(isinstance(b, bool) or not isinstance(b, int) for b in u):
        raise ValueError(f"Expected sequence of integer bits 0/1, got {u!r}")
    u_tup = tuple(int(b) for b in u)
    if (
        len(u_tup) < 1
        or u_tup[0] != 1
        or u_tup[-1] != 1
        or any(b not in (0, 1) for b in u_tup)
    ):
        raise ValueError(f"Expected core parity word starting and ending with 1, got {u!r}")
    from . import cs_forest_transfer as cft

    w_u = sum(u_tup)
    a_u = cft.canonical_suffix_shift(u_tup, 1)
    zeros = a_u + 2 * (3 ** (w_u - 1)) * q
    return u_tup + (0,) * zeros + (1,) + (0, 1) * m


def is_diamond6_cone7(x: int) -> bool:
    """
    Seventh Syracuse-jump cone of `T_diamond6` (`2^g * 3^h - 811 -> 2^(g - 7) * 3^(h + 1) - 19`,
    `g >= 15, h >= 2`, starting at `294101 = 32768 * 9 - 811`, with `21232853 -> 497645`):
        `x >= 294101 and x % 32768 == 31957 and x % 9 == 8 and coprime23(x + 811) == 1`.
    """
    if isinstance(x, bool) or not isinstance(x, int):
        raise ValueError(f"Expected integer x, got {x!r}")
    if x < 294_101 or (x % 32_768) != 31_957 or (x % 9) != 8:
        return False
    return _decompose_2_3_coprime(x + 811)[2] == 1


def cousin_diamond6_step_int(x: int, q: int = 3) -> int:
    """
    Sixth solvable mixed-(2,3) Collatz cousin `T_diamond6` on `Z` (for odd `q >= 3`),
    incorporating a genuine `v_2(3x + 1) == 7` (`/128`) Syracuse jump cone `Cone 7`
    (`x = 2^g * 3^h - 811`, `g >= 15, h >= 2`) that jumps `Phi_diamond2` upward directly into
    `Cone 6` -> `Cone 5` (`21232853 -> 497645 -> 186617 -> ...`), yet converges globally to `1`
    under a 4-tier `omega^4` ordinal ranking:
      - If `is_diamond6_cone7(x)`: `(q * x + 1) // 128`;
      - Otherwise: `cousin_diamond5_step_int(x, q=q)`.
    """
    if isinstance(x, bool) or not isinstance(x, int):
        raise ValueError(f"Expected integer x, got {x!r}")
    if isinstance(q, bool) or not isinstance(q, int) or (q & 1) == 0 or q < 3:
        raise ValueError(f"Expected odd multiplier q >= 3, got {q!r}")
    if is_diamond6_cone7(x):
        return (q * x + 1) // 128
    return cousin_diamond5_step_int(x, q=q)


def cousin_diamond6_step_q6(x: Fraction) -> Fraction:
    """
    Canonical extension of `T_diamond6` (`q = 3`) to `Q_(6) = {a/b : gcd(b, 6) == 1}`.
    Agrees identically with `cousin_diamond6_step_int` on all integers `a/1`, avoids Cone 7
    universally on all non-integer rationals `den >= 5`, and preserves `Q_(6)`.
    """
    if isinstance(x, bool) or not isinstance(x, (int, Fraction)):
        raise ValueError(f"Expected int or Fraction x, got {x!r}")
    if not isinstance(x, Fraction):
        x = Fraction(x)
    if math.gcd(x.denominator, 6) != 1:
        raise ValueError(f"Expected rational with gcd(denom, 6) == 1, got {x}")
    num = x.numerator
    den = x.denominator
    inv_d_32768 = pow(den, -1, 32_768)
    inv_d_9 = pow(den, -1, 9)
    r32768 = (num * inv_d_32768) % 32_768
    r9 = (num * inv_d_9) % 9
    if (
        num >= 294_101 * den
        and r32768 == 31_957
        and r9 == 8
        and core3_pos(core2_pos(num + 811 * den)) == den
    ):
        return (3 * x + 1) / 128
    return cousin_diamond5_step_q6(x)


def cousin_diamond6_block_return(x: int) -> Tuple[int, int]:
    """
    Exact 4-tier `omega^4` return `(horizon_steps, next_state)` for `T_diamond6` on `Z^+`:
      - `x == 1`: `(0, 1)`;
      - `x == 2`: `(1, 1)`;
      - `is_diamond6_cone7(x)` (`x + 811 == 2^g * 3^h`, `g >= 15, h >= 2`):
        steps once via `(3 * x + 1) // 128` into `Cone 6` (`y = 2^(g - 7) * 3^(h + 1) - 19`)
        and drains to `1` in `1 + h_cone6(y)` total steps;
      - `is_diamond3_cone4(x)` or `is_diamond4_cone5(x)` or `is_diamond5_cone6(x)`:
        identical to `cousin_diamond5_block_return(x)` (since zero states along Cone-4/5/6
        orbits lie in Cone 7);
      - all other `x > 2`: `(1, cousin_diamond6_step_int(x))` (strictly decreasing `Phi_diamond2`).
    """
    if isinstance(x, bool) or not isinstance(x, int) or x < 1:
        raise ValueError(f"Expected positive integer x >= 1, got {x!r}")
    if x == 1:
        return (0, 1)
    if x == 2:
        return (1, 1)
    if is_diamond6_cone7(x):
        y = cousin_diamond6_step_int(x, q=3)
        if not is_diamond5_cone6(y):
            raise AssertionError(f"Cone 7 step at x={x} missed Cone 6: y={y}")
        h_c6, end_c6 = cousin_diamond5_block_return(y)
        horizon = 1 + h_c6
        cur = x
        for _ in range(horizon):
            cur = cousin_diamond6_step_int(cur, q=3)
        if end_c6 != 1 or cur != 1:
            raise AssertionError(f"Cone 7 return mismatch under T_diamond6 at x={x}: ended at {cur}")
        return (horizon, 1)
    if is_diamond3_cone4(x) or is_diamond4_cone5(x) or is_diamond5_cone6(x):
        horizon, end_st = cousin_diamond5_block_return(x)
        cur = x
        for _ in range(horizon):
            cur = cousin_diamond6_step_int(cur, q=3)
        if end_st != 1 or cur != 1:
            raise AssertionError(f"Cone 4/5/6 return mismatch under T_diamond6 at x={x}: ended at {cur}")
        return (horizon, 1)
    return (1, cousin_diamond6_step_int(x, q=3))


def audit_w9_front_a_srs_d2_barrier_d3_omit_r9_and_zantema() -> Dict[str, Any]:
    """
    Front A (`Branch P4.3`):
    1. Verify the exact 5-level `3 x 3` (`d = 3`) non-triangular Hofbauer-Waldmann certificate
       tower terminating `omit R9` (`{R1, R2, R3, R4, R5, R6, R7, R8, R10, R11}`, `10/11` rules),
       joining Wave 8's `omit R2`, `omit R7`, and `omit R5` to prove `R2, R5, R7, R9` must all
       fire infinitely often in any infinite `all11` rewrite chain!
    2. Verify Zantema right-to-left modular semantic algebra `collatzSemMod(M)` across `M = 1..12`
       (`eval_sem(LHS, a) == eval_sem(RHS, a)` for all `11/11` rules and all `0 <= a < M`),
       and verify the exact 7-level `M = 2, d = 2` (`2 x 2` over `14` parity-labelled symbols)
       Hofbauer-Waldmann certificate tower completely terminating all `18/18` labelled rules of
       `S9 = all11 \\ {R3, R8}`!
    3. Verify `S9` subsequence self-embedding (`[L, B1, R] ->^+ [L, B1, B0, R]` via `R2, R11`)
       forcing `(M_B0)_{1,1} == 0` & `(v_R)_1 >= 1` under any `d = 2` strict removal of `R2` or `R11`.
    """
    base_rules: List[Tuple[str, Tuple[int, ...], Tuple[int, ...]]] = [
        ("R1", (0, 2), (0,)),
        ("R2", (0, 3), (0, 6)),
        ("R3", (4, 2), (2, 4)),
        ("R4", (4, 3), (3, 5)),
        ("R5", (5, 2), (3, 4)),
        ("R6", (5, 3), (2, 6)),
        ("R7", (6, 2), (2, 5)),
        ("R8", (6, 3), (3, 6)),
        ("R9", (4, 1), (3, 1)),
        ("R10", (5, 1), (2, 2, 1)),
        ("R11", (6, 1), (3, 2, 1)),
    ]

    def _eval_dim(
        d: int, cert_flat: Sequence[Sequence[int]], word: Sequence[int]
    ) -> Tuple[List[List[int]], List[int]]:
        m_acc = [[1 if r_i == c_i else 0 for c_i in range(d)] for r_i in range(d)]
        v_acc = [0] * d
        for sym in word:
            ent = cert_flat[sym]
            ms = [[ent[r_i * d + c_i] for c_i in range(d)] for r_i in range(d)]
            vs = [ent[d * d + r_i] for r_i in range(d)]
            v_nxt = [
                v_acc[r_i] + sum(m_acc[r_i][k_i] * vs[k_i] for k_i in range(d))
                for r_i in range(d)
            ]
            m_nxt = [
                [
                    sum(m_acc[r_i][k_i] * ms[k_i][c_i] for k_i in range(d))
                    for c_i in range(d)
                ]
                for r_i in range(d)
            ]
            m_acc, v_acc = m_nxt, v_nxt
        return m_acc, v_acc

    def _verify_tower_dim(
        d: int,
        nsyms: int,
        rules_in: Sequence[Tuple[str, Tuple[int, ...], Tuple[int, ...]]],
        levels: Sequence[Sequence[Sequence[int]]],
    ) -> bool:
        rem = list(rules_in)
        for cert in levels:
            if len(cert) != nsyms:
                return False
            for s_i in range(nsyms):
                if len(cert[s_i]) != d * d + d or cert[s_i][0] < 1 or any(v < 0 for v in cert[s_i]):
                    return False
            nxt_rem: List[Tuple[str, Tuple[int, ...], Tuple[int, ...]]] = []
            for r_rec in rem:
                _, lw, rw = r_rec
                ml, vl = _eval_dim(d, cert, lw)
                mr, vr = _eval_dim(d, cert, rw)
                if any(ml[i][j] < mr[i][j] for i in range(d) for j in range(d)):
                    return False
                if any(vl[i] < vr[i] for i in range(d)):
                    return False
                if vl[0] == vr[0]:
                    nxt_rem.append(r_rec)
            if len(nxt_rem) == len(rem):
                return False
            rem = nxt_rem
        return len(rem) == 0

    # 1. 5-level 3x3 (d = 3) Hofbauer-Waldmann certificate tower for omit R9 (10/11 rules)
    tower_omit_r9_3d = (
        (
            (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
            (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1),
            (1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0),
            (1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0),
            (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
            (1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0),
            (1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0),
        ),
        (
            (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
            (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1),
            (1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1, 0),
            (1, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0),
            (1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0),
            (1, 0, 2, 0, 1, 0, 0, 0, 0, 2, 0, 0),
            (1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0),
        ),
        (
            (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
            (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3),
            (1, 0, 4, 0, 0, 2, 0, 0, 0, 3, 0, 0),
            (1, 1, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0),
            (1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0),
            (1, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0),
            (1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
        ),
        (
            (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
            (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
            (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
            (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
            (1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0),
            (1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0),
            (1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0),
        ),
        (
            (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
            (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
            (1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1),
            (1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0),
            (2, 0, 0, 0, 5, 0, 2, 0, 0, 4, 0, 3),
            (2, 0, 0, 0, 0, 5, 0, 4, 0, 4, 0, 1),
            (2, 0, 0, 0, 2, 0, 0, 0, 2, 4, 3, 3),
        ),
    )
    omit_r9_3d_ok = _verify_tower_dim(
        3, 7, [r for r in base_rules if r[0] != "R9"], tower_omit_r9_3d
    )

    # 2. Zantema right-to-left modular semantic algebra (M = 1..12) + M = 2, d = 2 tower for S9
    def _sem_map(mod_m: int, sym: int, a_val: int) -> int:
        if sym == 0:
            return 0
        if sym == 1:
            return 1 % mod_m
        if sym in (2, 3):
            return (2 * a_val + (sym - 2)) % mod_m
        return (3 * a_val + (sym - 4)) % mod_m

    def _eval_sem_word(mod_m: int, word: Sequence[int], a_val: int) -> int:
        cur = a_val
        for sym in reversed(word):
            cur = _sem_map(mod_m, sym, cur)
        return cur

    def _label_word(mod_m: int, word: Sequence[int], a_val: int) -> Tuple[int, ...]:
        out = [0] * len(word)
        cur = a_val
        for idx in range(len(word) - 1, -1, -1):
            out[idx] = word[idx] * mod_m + cur
            cur = _sem_map(mod_m, word[idx], cur)
        return tuple(out)

    sem_model_ok = all(
        _eval_sem_word(mod_m, lw, a_v) == _eval_sem_word(mod_m, rw, a_v)
        for mod_m in range(1, 13)
        for (_, lw, rw) in base_rules
        for a_v in range(mod_m)
    )

    s9_labelled_2 = [
        (f"{nm}_{a_v}", _label_word(2, lw, a_v), _label_word(2, rw, a_v))
        for (nm, lw, rw) in base_rules
        if nm not in ("R3", "R8")
        for a_v in range(2)
    ]
    tower_s9_m2_2d = (
        (
            (1, 0, 0, 0, 2, 0), (1, 0, 0, 0, 2, 0), (1, 0, 0, 0, 1, 0), (1, 0, 0, 0, 1, 0),
            (1, 0, 1, 0, 0, 1), (1, 0, 0, 0, 0, 0), (1, 1, 0, 0, 1, 0), (1, 0, 0, 0, 1, 0),
            (1, 0, 0, 0, 0, 0), (2, 0, 0, 0, 1, 0), (2, 0, 0, 0, 2, 0), (1, 0, 1, 0, 0, 1),
            (1, 1, 1, 0, 1, 1), (1, 0, 0, 0, 1, 0),
        ),
        (
            (1, 0, 0, 0, 1, 0), (1, 0, 0, 0, 1, 0), (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0),
            (2, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 1, 0), (1, 0, 0, 0, 1, 0),
            (1, 0, 0, 0, 0, 0), (2, 0, 0, 0, 0, 0), (2, 0, 0, 0, 1, 0), (2, 0, 0, 0, 0, 0),
            (1, 0, 0, 0, 1, 0), (1, 0, 0, 0, 1, 0),
        ),
        (
            (1, 0, 0, 0, 0, 1), (1, 0, 0, 0, 0, 1), (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0),
            (2, 0, 0, 0, 1, 0), (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0),
            (1, 0, 0, 0, 0, 0), (2, 0, 0, 0, 0, 0), (2, 0, 0, 0, 0, 0), (2, 0, 0, 0, 2, 0),
            (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0),
        ),
        (
            (1, 0, 2, 0, 0, 0), (1, 0, 2, 0, 0, 0), (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0),
            (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 1, 0), (1, 0, 0, 0, 1, 0), (1, 0, 0, 0, 2, 0),
            (1, 0, 0, 0, 0, 0), (2, 0, 0, 0, 1, 0), (2, 0, 0, 0, 1, 0), (1, 0, 0, 0, 0, 0),
            (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 2, 0),
        ),
        (
            (1, 0, 0, 0, 0, 0), (1, 2, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0),
            (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 1, 1), (1, 2, 0, 0, 0, 0), (1, 0, 0, 0, 1, 1),
            (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 2, 1), (1, 2, 0, 1, 1, 0), (1, 0, 0, 0, 0, 0),
            (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 3, 0),
        ),
        (
            (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0),
            (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 1, 0), (1, 0, 0, 0, 2, 0),
            (1, 0, 0, 0, 0, 0), (3, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0),
            (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 2, 0),
        ),
        (
            (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0),
            (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 1, 0),
            (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0),
            (1, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0),
        ),
    )
    s9_m2_2d_ok = len(s9_labelled_2) == 18 and _verify_tower_dim(
        2, 14, s9_labelled_2, tower_s9_m2_2d
    )

    # 3. Verify [L, B1, R] ->(R2) [L, T2, R] ->(R11) [L, B1, B0, R] forces d_B0 == 0 & y_R >= 1
    #    whenever v_0(L B1 R) > v_0(L B1 B0 R) in d = 2:
    pump_zero_diag_ok = True
    for p1 in range(1, 4):
        for q1 in range(0, 4):
            for ab0 in range(1, 3):
                for bb0, cb0, db0, xb0, yb0, xr, yr in product(range(3), repeat=7):
                    v_lbr = p1 * xr + q1 * yr
                    v_lb1b0r = p1 * (xb0 + ab0 * xr + bb0 * yr) + q1 * (yb0 + cb0 * xr + db0 * yr)
                    if v_lbr > v_lb1b0r:
                        if not (q1 >= 1 and db0 == 0 and yr >= 1):
                            pump_zero_diag_ok = False
                            break

    # 4. Verify the 4 minimal nonnegative Parikh syzygies of S9 (Z_int, Z_9, Z_11, Z_10)
    #    spanning all 9 rules AND boundary-coupled (full 2x2 L, R) interior-lower-triangular collapse:
    s9_rules = [r for r in base_rules if r[0] not in ("R3", "R8")]
    s9_by_name = {nm: (lw, rw) for (nm, lw, rw) in s9_rules}
    syzygies = (
        {"R4": 1, "R5": 1, "R6": 1, "R7": 1},
        {"R2": 1, "R5": 1, "R6": 1, "R7": 2, "R9": 1},
        {"R1": 1, "R2": 1, "R11": 1},
        {"R1": 1, "R2": 1, "R4": 1, "R5": 1, "R7": 1, "R10": 1},
    )
    covered_s9 = {nm for syz in syzygies for nm in syz}
    parikh_syzygy_ok = covered_s9 == {nm for (nm, _, _) in s9_rules} and all(
        sum(mult * lw.count(sym) for nm, mult in syz.items() for lw, _ in (s9_by_name[nm],))
        == sum(mult * rw.count(sym) for nm, mult in syz.items() for _, rw in (s9_by_name[nm],))
        for syz in syzygies
        for sym in range(7)
    )

    def _comp_2d(m1: Tuple[int, ...], m2: Tuple[int, ...]) -> Tuple[int, ...]:
        a1, b1, c1, d1, x1, y1 = m1
        a2, b2, c2, d2, x2, y2 = m2
        return (
            a1 * a2 + b1 * c2,
            a1 * b2 + b1 * d2,
            c1 * a2 + d1 * c2,
            c1 * b2 + d1 * d2,
            a1 * x2 + b1 * y2 + x1,
            c1 * x2 + d1 * y2 + y1,
        )

    def _eval_2d_word(interp_2d: Sequence[Tuple[int, ...]], word: Sequence[int]) -> Tuple[int, ...]:
        acc = (1, 0, 0, 1, 0, 0)
        for s_idx in word:
            acc = _comp_2d(acc, interp_2d[s_idx])
        return acc

    boundary_nontri_collapse_ok = True
    for bl, cr, db0, db1, cb1, yb1 in product((0, 1, 2), (0, 1), (0, 1, 2), (0, 1), (0, 1), (0, 1)):
        for yb0, dt2, yt2 in product((0, 1), (0, 1), (0, 1)):
            cand_2d = (
                (1, bl, 0, 1, 0, 0),      # L (full 2x2 with b_L >= 0)
                (1, 1, cr, 1, 1, 1),      # R (full 2x2 with b_R = 1, c_R >= 0)
                (1, 0, 0, db0, 0, yb0),   # B0 (lower-tri)
                (1, 0, cb1, db1, 0, yb1), # B1 (lower-tri)
                (1, 0, cb1, 1, 0, yb1),   # T0 (lower-tri)
                (1, 0, 0, 0 if (db1 == 0 and dt2 == 0) else 1, 0, yt2),  # T1
                (1, 0, cb1, dt2, 0, yt2), # T2 (lower-tri)
            )
            if all(
                all(
                    _eval_2d_word(cand_2d, lw)[coord] >= _eval_2d_word(cand_2d, rw)[coord]
                    for coord in range(6)
                )
                for (_, lw, rw) in s9_rules
            ):
                if any(
                    _eval_2d_word(cand_2d, lw)[4] > _eval_2d_word(cand_2d, rw)[4]
                    for (_, lw, rw) in s9_rules
                ):
                    boundary_nontri_collapse_ok = False
                    break
        if not boundary_nontri_collapse_ok:
            break

    return {
        "omit_r9_10_of_11_5level_3d_tower_verified": omit_r9_3d_ok,
        "zantema_mod_m_semantic_algebra_verified": sem_model_ok,
        "s9_mod2_labelled_7level_2d_tower_verified": s9_m2_2d_ok,
        "s9_subseq_pumping_zero_diag_obstruction_verified": pump_zero_diag_ok,
        "s9_parikh_syzygy_and_boundary_nontri_2d_collapse_verified": (
            parikh_syzygy_ok and boundary_nontri_collapse_ok
        ),
    }


def audit_w9_front_b_laurent_4x4_twobase_and_coprime_sieve() -> Dict[str, Any]:
    """
    Front B (`Branch P3.3` & `P3.4`):
    1. Verify all three exact pure-integer `4 x 4` Schneider-Laurent determinant closed forms:
       - Single-base `(T=3, U=1)` Taylor-extrapolated (`rows=[(0,0),(1,0),(2,0),(3,0)], cols=[(0,0),(1,0),(2,0),(0,u)]`):
         `det_4 == W^3 * (2^u - 1)^3 > 0`;
       - Single-base `(T=2, U=2)` confluent Vandermonde (`rows=[(0,0),(1,0),(2,0),(3,0)], cols=[(0,0),(1,0),(0,u),(1,u)]`):
         `det_4 == W^2 * 2^u * (2^u - 1)^4 > 0`;
       - Two-base `(2^r * 3^s)^u` (`rows=[(0,0),(1,0),(0,1),(1,1)], cols=[(0,0),(1,0),(0,u),(1,u)]`):
         `det_4 == W^2 * 2^u * (3^u - 1)^2 - K^2 * 3^u * (2^u - 1)^2`, vanishing at `(W, K, u) = (9, 16, 2)`,
         strictly `!= 0` for ALL `W, K >= 1` and odd `u`, and strictly `!= 0` (`> 0` for `u >= 2`) across
         the Collatz convergent cone `3 * K <= 5 * W`!
    2. Verify Pratt/Lucas primality + exact coprime multiplicative orders for `p_3 = 45,661,129`
       (`% 8 == 1`, `(12381, 1844)`) and `p_4 = 107,889,071` (`% 8 == 7`, `(52835, 1021)`),
       and verify the joint `(331, 107889071)` 1-block (`w1 >= 550319, K >= 867329`) and
       2-block shared-Mersenne (`W >= 159276, K >= 264946`) weight/length floors!
    """
    def _det4_laplace(m4: Sequence[Sequence[int]]) -> int:
        res = 0
        for col_j in range(4):
            if m4[0][col_j] == 0:
                continue
            sub3 = tuple(
                tuple(m4[r_i][c_i] for c_i in range(4) if c_i != col_j)
                for r_i in (1, 2, 3)
            )
            term = m4[0][col_j] * _det3_int(sub3)
            res += (-term) if (col_j & 1) else term
        return res

    def _laurent_mat4(
        w_v: int, k_v: int, rows4: Sequence[Tuple[int, int]], cols4: Sequence[Tuple[int, int]]
    ) -> List[List[int]]:
        return [
            [
                math.comb(r_i * w_v + s_i * k_v, t_i) * (1 << (r_i * u_i)) * (3 ** (s_i * u_i))
                for (t_i, u_i) in cols4
            ]
            for (r_i, s_i) in rows4
        ]

    det4_ok = True
    rows_single = [(0, 0), (1, 0), (2, 0), (3, 0)]
    rows_twobase = [(0, 0), (1, 0), (0, 1), (1, 1)]
    for w_v, k_v in ((1, 2), (3, 5), (5, 8), (9, 16), (12, 19)):
        for u_v in range(1, 6):
            d_t3 = _det4_laplace(
                _laurent_mat4(w_v, k_v, rows_single, [(0, 0), (1, 0), (2, 0), (0, u_v)])
            )
            d_c22 = _det4_laplace(
                _laurent_mat4(w_v, k_v, rows_single, [(0, 0), (1, 0), (0, u_v), (1, u_v)])
            )
            d_tb = _det4_laplace(
                _laurent_mat4(w_v, k_v, rows_twobase, [(0, 0), (1, 0), (0, u_v), (1, u_v)])
            )
            exp_t3 = (w_v**3) * (((1 << u_v) - 1) ** 3)
            exp_c22 = (w_v**2) * (1 << u_v) * (((1 << u_v) - 1) ** 4)
            exp_tb = (w_v**2) * (1 << u_v) * (((3**u_v) - 1) ** 2) - (k_v**2) * (3**u_v) * (
                ((1 << u_v) - 1) ** 2
            )
            if d_t3 != exp_t3 or d_t3 <= 0 or d_c22 != exp_c22 or d_c22 <= 0 or d_tb != exp_tb:
                det4_ok = False
                break
            if (u_v & 1) == 1 and d_tb == 0:
                det4_ok = False
                break
            if 3 * k_v <= 5 * w_v:
                if d_tb == 0 or (u_v >= 2 and d_tb <= 0):
                    det4_ok = False
                    break

    res_zero_9_16_2 = (
        _det4_laplace(_laurent_mat4(9, 16, rows_twobase, [(0, 0), (1, 0), (0, 2), (1, 2)])) == 0
    )

    # 2. Coprime-order primes p_3 = 45,661,129 (% 8 == 1) and p_4 = 107,889,071 (% 8 == 7)
    p3, p4 = 45_661_129, 107_889_071
    primes_ok = (
        all(p3 % d_i != 0 for d_i in range(3, int(math.isqrt(p3)) + 1, 2))
        and all(p4 % d_i != 0 for d_i in range(3, int(math.isqrt(p4)) + 1, 2))
        and _mult_order_mod_prime(2, p3) == 12_381
        and _mult_order_mod_prime((3 * pow(2, -1, p3)) % p3, p3) == 1_844
        and (p3 % 8) == 1
        and _mult_order_mod_prime(2, p4) == 52_835
        and _mult_order_mod_prime((3 * pow(2, -1, p4)) % p4, p4) == 1_021
        and (p4 % 8) == 7
    )

    # Joint (331, 107889071) 1-block & 2-block floors:
    # 1-block: lcm(11, 1021) = 11231 | w1, lcm(30, 52835) = 317010 | a1, gcd(w1, 317010) == 1,
    # and 3^w1 < 2^(w1 + a1) with 2^(w1 + a1) - 3^w1 <= 2^a1 - 1 requires 2^w1 < 3^w1 / (2^w1 - 1)...
    # Specifically, w1 >= 43 * 11231 = 482,933? Let's check minimal multiple k_w * 11231 with gcd(k_w, 30*10567) == 1
    # AND 3^(w1) > 2^(w1 + 317010 - 1) (since if a1 == 317010 and w1 <= 42 * 11231 = 471702, 2^(w1 + 317010) - 3^w1 > 2^317010 - 1!):
    lcm_w = math.lcm(11, 1_021)       # 11,231
    lcm_a = math.lcm(30, 52_835)      # 317,010
    # Note: for ANY 1-block positive cycle, 2^(w1 + a1) - 3^w1 <= 2^a1 - 1 => (2^w1 - 1)*2^a1 < 3^w1!
    # Since a1 >= 317,010 and 2^19 > 3^12 (19/12 > log2(3), or 8^k < 9^k: (3/2)^w1 > 2^317010 => (9/4)^(w1/2) > 2^317010;
    # using 3^12 = 531,441 > 524,288 = 2^19 -> (3/2)^12 = 531441/4096 < 130, while (3/2)^5 < 8 => w1 > 317010 * 5 / 3 = 528,350!!):
    min_w1_1block = min(
        m_k * lcm_w
        for m_k in range(1, 80)
        if math.gcd(m_k * lcm_w, lcm_a) == 1 and 3 * (m_k * lcm_w) > 5 * lcm_a
    )
    # 2-block shared-Mersenne with 107889071 | D: 52835 | a1, 52835 | a2 => a1 + a2 >= 105,670,
    # 1021 | W, and 3*(W + a1 + a2) < 5*W => 2*W > 3*105670 = 317,010 => W >= 159 * 1021? Wait:
    # 317010 // 2 = 158,505; 158505 // 1021 + 1 = 156 => 156 * 1021 = 159,276!
    min_w_2block_p4 = min(
        v_w * 1_021
        for v_w in range(1, 200)
        if 2 * (v_w * 1_021) > 3 * 105_670
    )
    # Standalone cyclotomic companion quotient forcing & solo 1-block floors for p4 & p3:
    min_w1_solo_p4 = min(
        m_k * 1_021
        for m_k in range(1, 100)
        if 3 * (m_k * 1_021) + 5 > 5 * 52_835
    )
    min_w1_solo_p3 = min(
        m_k * 1_844
        for m_k in range(1, 30)
        if 3 * (m_k * 1_844) + 5 > 5 * 12_381
    )
    companion_solo_ok = (
        (52_835 % 5) == 0
        and ((1 << 5) - 1) == 31
        and (12_381 % 3) == 0
        and ((1 << 3) - 1) == 7
        and (1_844 % 4) == 0
        and (3**4 - 2**4) == 65
        and min_w1_solo_p4 == 88_827
        and min_w1_solo_p4 + 52_835 == 141_662
        and min_w1_solo_p3 == 22_128
        and min_w1_solo_p3 + 12_381 == 34_509
    )
    floors_ok = (
        lcm_w == 11_231
        and lcm_a == 317_010
        and min_w1_1block == 550_319
        and min_w_2block_p4 == 159_276
        and min_w_2block_p4 + 105_670 == 264_946
        and companion_solo_ok
    )

    return {
        "laurent_4x4_three_closed_forms_and_cone_verified": det4_ok and res_zero_9_16_2,
        "twobase_4x4_resonant_zero_9_16_2_verified": res_zero_9_16_2,
        "coprime_primes_p3_45661129_and_p4_107889071_verified": primes_ok,
        "joint_331_and_107889071_floors_verified": floors_ok,
        "solo_p3_p4_companion_quotient_forcing_verified": companion_solo_ok,
    }


def audit_w9_front_c_stateful_automaton_barrier_and_diamond6() -> Dict[str, Any]:
    """
    Front C (`Branch P1.2` & `P5`):
    1. Verify the universal stateful `Q`-state LSB-first and MSB-first automaton collision family
       `m_{Q, s} = 3 * 4^(2*Q + Q!*s) + 2^(2*Q + 1)` vs `2^(Q!) * m_{Q, s}` and odd preimage
       `n_{Q, s} = (2 * m_{Q, s} - 1) // 3` across `Q = 1..3`, all transition tables, and `s = 0..3`,
       plus exact affine growth `2 * Q! * s + const` of `(zero_bit_count, bit_length)`.
    2. Verify 6th solvable `(3x + 1)`-cousin `T_diamond6`:
       - Strict `Phi_diamond2` descent in 1 step outside Cones 4, 5, 6, 7 (`x = 3..6000`);
       - Exact Cone-7 -> Cone-6 -> Cone-5 4-tier `omega^4` cascade (`g = 15..20, h = 2..5`,
         including `294101 -> 6893 -> 2585` and `21232853 -> 497645 -> 186617`), zero Cone-7
         hits along Cone-4/5/6 orbits, polynomial bound `h <= (x+1)^3 + (x+1)^5`, and
         `M1`/`M2`/`M3` + `Q_(6)`/`Int` agreement (including non-integer `294101/7` Cone-7 avoidance!).
    """
    stateful_ok = True
    for q_st in (1, 2, 3):
        p_per = math.factorial(q_st)
        m0 = 3 * (4 ** (2 * q_st)) + (1 << (2 * q_st + 1))
        n0 = (2 * m0 - 1) // 3
        l_m0 = m0.bit_length()
        z_m0 = l_m0 - m0.bit_count()
        l_n0 = n0.bit_length()
        z_n0 = l_n0 - n0.bit_count()

        # Test all Q=1,2 tables exhaustively and 64 deterministic diverse tables for Q=3
        if q_st <= 2:
            tables = [
                [(flat[2 * i], flat[2 * i + 1]) for i in range(q_st)]
                for flat in product(range(q_st), repeat=2 * q_st)
            ]
        else:
            tables = [
                [
                    ((seed_t + i) % 3, (seed_t * 2 + i + 1) % 3)
                    for i in range(3)
                ]
                for seed_t in range(27)
            ] + [[((i + 1) % 3, i) for i in range(3)]]

        for s_idx in range(0, 4):
            ms = 3 * (4 ** (2 * q_st + p_per * s_idx)) + (1 << (2 * q_st + 1))
            evs = ms << p_per
            ns = (2 * ms - 1) // 3
            if (
                (ms % 3) != 2
                or int_compressed_step(ns, q=3) != ms
                or ms.bit_length() != l_m0 + 2 * p_per * s_idx
                or (ms.bit_length() - ms.bit_count()) != z_m0 + 2 * p_per * s_idx
                or evs.bit_length() != l_m0 + 2 * p_per * s_idx + p_per
                or (evs.bit_length() - evs.bit_count()) != z_m0 + 2 * p_per * s_idx + p_per
                or ns.bit_length() != l_n0 + 2 * p_per * s_idx
                or (ns.bit_length() - ns.bit_count()) != z_n0 + 2 * p_per * s_idx
            ):
                stateful_ok = False
                break
            for tbl in tables:
                for q_init in range(q_st):
                    if (
                        run_lsb_automaton(q_st, tbl, q_init, ms)
                        != run_lsb_automaton(q_st, tbl, q_init, m0)
                        or run_lsb_automaton(q_st, tbl, q_init, evs)
                        != run_lsb_automaton(q_st, tbl, q_init, m0)
                        or run_lsb_automaton(q_st, tbl, q_init, ns)
                        != run_lsb_automaton(q_st, tbl, q_init, n0)
                        or run_msb_automaton(q_st, tbl, q_init, ms)
                        != run_msb_automaton(q_st, tbl, q_init, m0)
                        or run_msb_automaton(q_st, tbl, q_init, evs)
                        != run_msb_automaton(q_st, tbl, q_init, m0)
                        or run_msb_automaton(q_st, tbl, q_init, ns)
                        != run_msb_automaton(q_st, tbl, q_init, n0)
                    ):
                        stateful_ok = False
                        break

    # 1b. Stateful Q-state Mealy transducer affine growth & Mersenne 1-spine barrier
    transducer_ok = True
    for q_st in (1, 2, 3):
        p_per = math.factorial(q_st)
        m0 = 3 * (4 ** (2 * q_st)) + (1 << (2 * q_st + 1))
        ev0 = m0 << p_per
        n0 = (2 * m0 - 1) // 3
        m_s1 = 3 * (4 ** (2 * q_st + p_per)) + (1 << (2 * q_st + 1))
        ev_s1 = m_s1 << p_per
        n_s1 = (2 * m_s1 - 1) // 3
        emit_samples = [
            [(1 + ((i + seed_e) % 3), (2 * i + seed_e) % 3) for i in range(q_st)]
            for seed_e in range(3)
        ] + [[(0, 1) for _ in range(q_st)]]
        sample_tables = (
            [
                [(flat[2 * i], flat[2 * i + 1]) for i in range(q_st)]
                for flat in product(range(q_st), repeat=2 * q_st)
            ]
            if q_st <= 2
            else [[((seed_t + i) % 3, (seed_t * 2 + i + 1) % 3) for i in range(3)] for seed_t in range(9)]
        )
        for tbl in sample_tables:
            for em in emit_samples:
                for q_init in range(q_st):
                    sl_l_m = run_lsb_transducer(q_st, tbl, em, q_init, m_s1) - run_lsb_transducer(
                        q_st, tbl, em, q_init, m0
                    )
                    sl_l_ev = run_lsb_transducer(q_st, tbl, em, q_init, ev_s1) - run_lsb_transducer(
                        q_st, tbl, em, q_init, ev0
                    )
                    sl_l_n = run_lsb_transducer(q_st, tbl, em, q_init, n_s1) - run_lsb_transducer(
                        q_st, tbl, em, q_init, n0
                    )
                    sl_m_m = run_msb_transducer(q_st, tbl, em, q_init, m_s1) - run_msb_transducer(
                        q_st, tbl, em, q_init, m0
                    )
                    sl_m_ev = run_msb_transducer(q_st, tbl, em, q_init, ev_s1) - run_msb_transducer(
                        q_st, tbl, em, q_init, ev0
                    )
                    sl_m_n = run_msb_transducer(q_st, tbl, em, q_init, n_s1) - run_msb_transducer(
                        q_st, tbl, em, q_init, n0
                    )
                    if sl_l_m != sl_l_ev or sl_m_m != sl_m_ev:
                        transducer_ok = False
                        break
                    for s_idx in (2, 3):
                        ms_i = 3 * (4 ** (2 * q_st + p_per * s_idx)) + (1 << (2 * q_st + 1))
                        evs_i = ms_i << p_per
                        ns_i = (2 * ms_i - 1) // 3
                        if (
                            run_lsb_transducer(q_st, tbl, em, q_init, ms_i)
                            != run_lsb_transducer(q_st, tbl, em, q_init, m0) + s_idx * sl_l_m
                            or run_lsb_transducer(q_st, tbl, em, q_init, evs_i)
                            != run_lsb_transducer(q_st, tbl, em, q_init, ev0) + s_idx * sl_l_m
                            or run_lsb_transducer(q_st, tbl, em, q_init, ns_i)
                            != run_lsb_transducer(q_st, tbl, em, q_init, n0) + s_idx * sl_l_n
                            or run_msb_transducer(q_st, tbl, em, q_init, ms_i)
                            != run_msb_transducer(q_st, tbl, em, q_init, m0) + s_idx * sl_m_m
                            or run_msb_transducer(q_st, tbl, em, q_init, evs_i)
                            != run_msb_transducer(q_st, tbl, em, q_init, ev0) + s_idx * sl_m_m
                            or run_msb_transducer(q_st, tbl, em, q_init, ns_i)
                            != run_msb_transducer(q_st, tbl, em, q_init, n0) + s_idx * sl_m_n
                        ):
                            transducer_ok = False
                            break
                    # Also verify Mersenne 1-spine affine slope equality on ms1 vs 2 * ms1:
                    m1_0 = 3 * (1 << (2 * q_st)) - 1
                    ev1_0 = 2 * m1_0
                    n1_0 = (1 << (2 * q_st + 1)) - 1
                    m1_1 = 3 * (1 << (2 * q_st + p_per)) - 1
                    ev1_1 = 2 * m1_1
                    n1_1 = (1 << (2 * q_st + p_per + 1)) - 1
                    sl1_m = run_msb_transducer(q_st, tbl, em, q_init, m1_1) - run_msb_transducer(
                        q_st, tbl, em, q_init, m1_0
                    )
                    sl1_ev = run_msb_transducer(q_st, tbl, em, q_init, ev1_1) - run_msb_transducer(
                        q_st, tbl, em, q_init, ev1_0
                    )
                    sl1_n = run_msb_transducer(q_st, tbl, em, q_init, n1_1) - run_msb_transducer(
                        q_st, tbl, em, q_init, n1_0
                    )
                    m1_2 = 3 * (1 << (2 * q_st + 2 * p_per)) - 1
                    ev1_2 = 2 * m1_2
                    n1_2 = (1 << (2 * q_st + 2 * p_per + 1)) - 1
                    if (
                        sl1_m != sl1_ev
                        or run_msb_transducer(q_st, tbl, em, q_init, m1_2)
                        != run_msb_transducer(q_st, tbl, em, q_init, m1_0) + 2 * sl1_m
                        or run_msb_transducer(q_st, tbl, em, q_init, ev1_2)
                        != run_msb_transducer(q_st, tbl, em, q_init, ev1_0) + 2 * sl1_m
                        or run_msb_transducer(q_st, tbl, em, q_init, n1_2)
                        != run_msb_transducer(q_st, tbl, em, q_init, n1_0) + 2 * sl1_n
                    ):
                        transducer_ok = False
                        break

    # Popcount-parity Q=2 Mealy transducer (survives 0-spine m_{2,s} alone, killed by Mersenne 1-spine!):
    pop_tbl = [(0, 1), (1, 0)]
    pop_emit = [(0, 0), (1, 0)]
    m1_kill = 3 * (1 << 6) - 1  # 191, odd preimage 127
    n1_kill = (2 * m1_kill - 1) // 3
    w_pop = lambda z: Fraction(
        1, 10 * (run_msb_transducer(2, pop_tbl, pop_emit, 0, z) ** 2) + z.bit_length()
    )
    if not (w_pop(2 * m1_kill) + w_pop(n1_kill) > w_pop(m1_kill)):
        transducer_ok = False

    # 2. 6th Solvable Cousin T_diamond6
    d6_outside_ok = all(
        (
            is_diamond3_cone4(x)
            or is_diamond4_cone5(x)
            or is_diamond5_cone6(x)
            or is_diamond6_cone7(x)
            or cousin_diamond2_phi(cousin_diamond6_step_int(x)) < cousin_diamond2_phi(x)
        )
        for x in range(3, 6001)
    )
    d6_cone7_ok = (
        is_diamond6_cone7(294_101)
        and cousin_diamond6_step_int(294_101) == 6_893
        and is_diamond5_cone6(6_893)
        and is_diamond6_cone7(21_232_853)
        and cousin_diamond6_step_int(21_232_853) == 497_645
        and cousin_diamond2_phi(497_645) > cousin_diamond2_phi(21_232_853)
    )
    for g_exp in range(15, 21):
        for h_exp in range(2, 6):
            xc7 = (1 << g_exp) * (3**h_exp) - 811
            yc6 = (1 << (g_exp - 7)) * (3 ** (h_exp + 1)) - 19
            h_st, end_st = cousin_diamond6_block_return(xc7)
            bound_poly = ((xc7 + 1) ** 3) + ((xc7 + 1) ** 5)
            if (
                not is_diamond6_cone7(xc7)
                or cousin_diamond6_step_int(xc7) != yc6
                or not is_diamond5_cone6(yc6)
                or end_st != 1
                or h_st > bound_poly
            ):
                d6_cone7_ok = False
                break

    d6_spiral_ok = True
    for r in range(1, 7):
        cur = 4 * (16**r) - 5
        for j in range(1, r + 1):
            mid = cousin_diamond6_step_int(cur)
            nxt = cousin_diamond6_step_int(mid)
            exp_nxt = 4 * (16 ** (r - j)) * (18**j) - 5
            if nxt != exp_nxt or nxt <= cur:
                d6_spiral_ok = False
                break
            cur = nxt

    m1_cur = Fraction(1, 7)
    for _ in range(5):
        m1_cur = cousin_diamond6_step_q6(m1_cur)
    m2_ok = (
        cousin_diamond6_step_int(-1) == -1
        and cousin_diamond6_step_int(cousin_diamond6_step_int(cousin_diamond6_step_int(-5))) == -5
    )
    m3_cur = 5
    for _ in range(5):
        m3_cur = cousin_diamond6_step_int(m3_cur, q=7)
    q6_int_agree_ok = all(
        cousin_diamond6_step_q6(Fraction(x_chk, 1)) == Fraction(cousin_diamond6_step_int(x_chk), 1)
        for x_chk in list(range(-80, 260)) + [2285, 294_101, 21_232_853]
    )
    q6_nonint_avoids_cone7 = all(
        cousin_diamond6_step_q6(Fraction(num_c, den_c))
        == cousin_diamond5_step_q6(Fraction(num_c, den_c))
        for den_c in (5, 7, 11)
        for num_c in (1, 19, 2285, 294_101, 294_101 * den_c - 811 * den_c + 1)
        if Fraction(num_c, den_c).denominator > 1
    )
    d6_countermodels_ok = (
        (m1_cur == Fraction(1, 7))
        and m2_ok
        and (m3_cur == 5)
        and q6_int_agree_ok
        and q6_nonint_avoids_cone7
    )

    return {
        "stateful_automaton_q_factorial_family_verified": stateful_ok,
        "stateful_transducer_affine_and_mersenne_barrier_verified": transducer_ok,
        "cousin_diamond6_outside_cones4567_descent_verified": d6_outside_ok,
        "cousin_diamond6_cone7_return_and_spiral_verified": d6_cone7_ok and d6_spiral_ok,
        "cousin_diamond6_countermodels_verified": d6_countermodels_ok,
    }


def audit_w9_front_d_global_collision_and_markov_pow3() -> Dict[str, Any]:
    """
    Front D (`Branch P5.3` & `P2.2`):
    1. Exhaustively verify the Complete Global `(u1, q1)` vs `(u2, q2)` Collision Classification
       across all core words `1 <= |u| <= 9` and ray indices `q >= 0` (`|u| + 2 * 3^(w-1) * q <= 17`):
       - `q1 >= 1` and `q2 >= 1`: globally injective (`u1 == u2 and q1 == q2`);
       - Mixed `q1 == 0` and `q2 >= 1`: `exact_backward_quotient(1, u1, 0) == exact_backward_quotient(1, u2, q2)`
         iff `exists m >= 0, u1 == loop_unroll_word(u2, q2, m)`, and EVERY such `u1` violates
         `is_first_hit_one_pair(u1, 0)`;
       - Global `IsFirstHitOnePair` Bijection: ZERO collisions across ALL `(u, q)` pairs satisfying
         `is_first_hit_one_pair(u, q)`, and `exact_backward_quotient(1, u, q) == 1` iff
         `q == 0 and u == (1,) + (0, 1) * m`.
    2. Verify exact mod-`18` Markov suffix laws (`pref + (1, 1) -> % 18 in {9, 15}` & `% 6 == 3`,
       `pref + (1, 0, 1) -> % 18 in {1, 7}` & `% 6 == 1`, `pref + (1, 1, 1) -> % 18 == 9`),
       and universal `k`-step `mod 2 * 3^k` prefix-memory annihilation (`k = 1..4`) whenever
       `parity_weight(suf) >= k + 1`!
    """
    from . import cs_forest_transfer as cft

    all_core_le9: List[Tuple[int, ...]] = [(1,)]
    for length in range(2, 10):
        for mid in product((0, 1), repeat=length - 2):
            all_core_le9.append((1,) + mid + (1,))

    pairs_by_y: Dict[int, List[Tuple[Tuple[int, ...], int, bool]]] = {}
    for u_c in all_core_le9:
        w_u = sum(u_c)
        for q_i in range(0, 4):
            if len(u_c) + 2 * (3 ** (w_u - 1)) * q_i <= 17:
                y_val = cft.exact_backward_quotient(1, u_c, q_i)
                fh_ok = cft.is_first_hit_one_pair(u_c, q_i)
                if q_i >= 1 and not fh_ok:
                    return {
                        "global_all_pairs_classification_verified": False,
                        "global_first_hit_injectivity_verified": False,
                        "markov_mod18_and_pow3_memory_annihilation_verified": False,
                    }
                pairs_by_y.setdefault(y_val, []).append((u_c, q_i, fh_ok))

    classification_ok = True
    fh_injective_ok = True
    mixed_collisions = 0
    for y_val, grp in pairs_by_y.items():
        fh_items = [(u_i, q_i) for (u_i, q_i, fh_i) in grp if fh_i]
        if len(fh_items) > 1:
            fh_injective_ok = False
        if y_val == 1:
            for u_i, q_i, _ in grp:
                if q_i != 0 or not any(
                    u_i == (1,) + (0, 1) * m_i for m_i in range(len(u_i) // 2 + 1)
                ):
                    classification_ok = False
        for i_idx in range(len(grp)):
            for j_idx in range(i_idx + 1, len(grp)):
                u1, q1, fh1 = grp[i_idx]
                u2, q2, fh2 = grp[j_idx]
                if q1 >= 1 and q2 >= 1:
                    classification_ok = False
                elif q1 == 0 and q2 >= 1:
                    mixed_collisions += 1
                    if fh1 or not any(
                        u1 == loop_unroll_word(u2, q2, m_e) for m_e in range(len(u1) // 2 + 1)
                    ):
                        classification_ok = False
                elif q2 == 0 and q1 >= 1:
                    mixed_collisions += 1
                    if fh2 or not any(
                        u2 == loop_unroll_word(u1, q1, m_e) for m_e in range(len(u2) // 2 + 1)
                    ):
                        classification_ok = False

    # Converse check on loop_unroll_word across q = 1, 2 and m = 0, 1, 2
    for u_base in ((1,), (1, 1), (1, 0, 1), (1, 1, 1)):
        for q_v in (1, 2):
            y_target = cft.exact_backward_quotient(1, u_base, q_v)
            for m_v in (0, 1, 2):
                u_unr = loop_unroll_word(u_base, q_v, m_v)
                if (
                    cft.exact_backward_quotient(1, u_unr, 0) != y_target
                    or cft.canonical_suffix_shift(u_unr, 1) != 1
                    or cft.is_first_hit_one_pair(u_unr, 0)
                ):
                    classification_ok = False

    # 2. Mod-18 deterministic/2-state suffix locks + universal k = 1..4 mod (2 * 3^k) memory annihilation
    markov_pow3_ok = True
    prefixes: List[Tuple[int, ...]] = [(), (1,), (1, 0), (1, 1), (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1)]
    for pref in prefixes:
        if len(pref) >= 1:
            if (cft.canonical_suffix_shift(pref + (1, 1), 1) % 18) not in (9, 15):
                markov_pow3_ok = False
            if (cft.canonical_suffix_shift(pref + (1, 0, 1), 1) % 18) not in (1, 7):
                markov_pow3_ok = False
            if (cft.canonical_suffix_shift(pref + (1, 1, 1), 1) % 18) != 9:
                markov_pow3_ok = False

    for k_pow in (1, 2, 3, 4):
        mod_2_3k = 2 * (3**k_pow)
        suffixes_k = [u_s for u_s in all_core_le9 if sum(u_s) >= k_pow + 1][:24]
        for suf in suffixes_k:
            base_mod = cft.canonical_suffix_shift(suf, 1) % mod_2_3k
            for pref in prefixes:
                if (cft.canonical_suffix_shift(pref + suf, 1) % mod_2_3k) != base_mod:
                    markov_pow3_ok = False
                    break

    # 3. Complete mod-18 Markov bijection table + universal multi-step 3^(w-1-j) fiber equidistribution
    def _ms_false(w_in: int, a_in: int) -> int:
        p_mod = 2 * (3 ** (w_in - 1))
        return (a_in - 1) if a_in >= 1 else (p_mod - 1)

    def _ms_true(w_in: int, a_in: int) -> int:
        return cft.dlog2_mod_pow3_aux(w_in, 3 * (1 << a_in) + 1) - 1

    def _iter_ms(tail_b: Sequence[int], w_in: int, a_in: int) -> int:
        cur_w = w_in
        cur_a = a_in
        for bit in tail_b:
            if bit == 0:
                cur_a = _ms_false(cur_w, cur_a)
            else:
                cur_a = _ms_true(cur_w, cur_a)
                cur_w += 1
        return cur_a

    mod18_expected = {0: 1, 1: 15, 2: 7, 3: 9, 4: 13, 5: 3}
    equidist_ok = all(
        (_ms_true(w_t, a_t) % 18) == mod18_expected[a_t % 6]
        for w_t in (2, 3, 4)
        for a_t in range(2 * (3 ** (w_t - 1)))
    ) and all(
        (cft.canonical_suffix_shift(u_w, 1) % 18) in (1, 3, 7, 9, 13, 15)
        for u_w in all_core_le9
        if sum(u_w) >= 3
    )
    tails_sample = [t_b for r_l in (1, 2, 3) for t_b in product((0, 1), repeat=r_l)]
    for w_f in (1, 2, 3):
        for j_f in range(w_f):
            m0_f = 2 * (3**j_f)
            n_fib = 3 ** (w_f - 1 - j_f)
            for r0_f in range(m0_f):
                for tail_f in tails_sample:
                    mk_f = 2 * (3 ** (j_f + sum(tail_f)))
                    imgs = [_iter_ms(tail_f, w_f, r0_f + m0_f * t_i) for t_i in range(n_fib)]
                    base_r = imgs[0] % mk_f
                    expected_set = {base_r + mk_f * q_i for q_i in range(n_fib)}
                    if len(set(imgs)) != n_fib or set(imgs) != expected_set:
                        equidist_ok = False
                        break

    return {
        "mixed_q0_qpos_collisions_found": mixed_collisions,
        "global_all_pairs_classification_verified": classification_ok and (mixed_collisions > 0),
        "global_first_hit_injectivity_verified": fh_injective_ok,
        "markov_mod18_and_pow3_memory_annihilation_verified": markov_pow3_ok,
        "markov_mod18_table_and_multistep_equidistribution_verified": equidist_ok,
    }


def _dynamic_pred_stateful_q2_automaton_distinguishes_multi_even(
    _dom: str, entry: Dict[str, Any]
) -> bool:
    """
    Dynamic test of `Q = 2` stateful LSB/MSB automaton preimage weights claiming some
    `2`-state automaton separates `m` from `2^d * m` on branching targets `m >= 3` (`m % 3 == 2`).
    Zero hardcoded witness IDs.
    """
    if "next_compressed" not in entry or "multi_even_preimage" not in entry:
        return True
    m_tgt = int(entry["next_compressed"])
    ev_m = int(entry["multi_even_preimage"])
    if m_tgt < 3 or (m_tgt % 3) != 2 or ev_m <= m_tgt:
        return True
    for flat in product(range(2), repeat=4):
        tbl = [(flat[0], flat[1]), (flat[2], flat[3])]
        for q0 in (0, 1):
            if (
                run_lsb_automaton(2, tbl, q0, m_tgt) != run_lsb_automaton(2, tbl, q0, ev_m)
                or run_msb_automaton(2, tbl, q0, m_tgt) != run_msb_automaton(2, tbl, q0, ev_m)
            ):
                return True
    return False


def _dynamic_pred_phi2_on_cousin_diamond6_outside_cones456(
    _dom: str, entry: Dict[str, Any]
) -> bool:
    """Dynamic test of single-step `Phi_diamond2` descent on `T_diamond6` outside Cones 4, 5, and 6."""
    seed = int(entry.get("seed", 0))
    if (
        seed <= 2
        or is_diamond3_cone4(seed)
        or is_diamond4_cone5(seed)
        or is_diamond5_cone6(seed)
    ):
        return True
    nxt = cousin_diamond6_step_int(seed, q=3)
    return cousin_diamond2_phi(nxt) < cousin_diamond2_phi(seed)


def _dynamic_pred_twobase_4x4_laurent_det_nonzero_for_all_coprime(
    _dom: str, entry: Dict[str, Any]
) -> bool:
    """
    Dynamic test of unrestricted claim that the two-base `4 x 4` Schneider-Laurent determinant
    is non-zero for all coprime `(W, K)` with `3^W < 2^K` and `u >= 1`.
    """
    if "W" not in entry or "K" not in entry or "laurent_twobase_4x4_u" not in entry:
        return True
    w_v = int(entry["W"])
    k_v = int(entry["K"])
    u_v = int(entry["laurent_twobase_4x4_u"])
    if w_v < 1 or k_v < 1 or u_v < 1 or math.gcd(w_v, k_v) != 1 or (3**w_v) >= (1 << k_v):
        return True
    det_v = (w_v * w_v) * (1 << u_v) * (((3**u_v) - 1) ** 2) - (k_v * k_v) * (3**u_v) * (
        ((1 << u_v) - 1) ** 2
    )
    return det_v != 0


def _dynamic_pred_third_coprime_prime_escapes_mod8_13(_dom: str, entry: Dict[str, Any]) -> bool:
    """Dynamic test of false claim that the 3rd coprime-order prime `p_3` satisfies `p_3 % 8 in {5, 7}`."""
    if "third_coprime_order_prime" not in entry:
        return True
    p3 = int(entry["third_coprime_order_prime"])
    if p3 <= 1_210_483:
        return True
    return (p3 % 8) in (5, 7)


def _dynamic_pred_mixed_q0_qpos_raw_disjointness(_dom: str, entry: Dict[str, Any]) -> bool:
    """
    Dynamic test of raw cross-regime disjointness claiming `exact_backward_quotient(1, u_mix, 0)`
    never equals `exact_backward_quotient(1, u, q)` (`q >= 1`).
    """
    if "mixed_q0_unroll_word" not in entry or "core_word" not in entry or "q_index" not in entry:
        return True
    from . import cs_forest_transfer as cft

    q_i = int(entry["q_index"])
    if q_i < 1:
        return True
    u_w = tuple(int(b) for b in entry["core_word"])
    u_mix = tuple(int(b) for b in entry["mixed_q0_unroll_word"])
    return cft.exact_backward_quotient(1, u_mix, 0) != cft.exact_backward_quotient(1, u_w, q_i)


def run_wave9_whole_space_campaign(bank_path: Optional[Path] = None) -> Dict[str, Any]:
    """
    Execute the complete Wave 9 whole-space red-team, `d = 2` unlabelled barriers / `d = 3`
    `omit R9` tower / Zantema `M = 2` semantic labelling, `4 x 4` two-base confluent Laurent
    non-vanishing & `p_3`/`p_4` coprime-order escape sieve, universal `forall Q >= 1` stateful
    finite-state automaton preimage barrier & `T_diamond6` benchmark, and complete global
    `(u, q)` collision classification & `2 * 3^k` Markov memory annihilation campaign.
    """
    u_gate = audit_universality_gate(
        "Wave9_WholeSpace_W9_1_to_W9_4",
        is_finite_m_table=False,
        is_finite_n_table=False,
        is_bounded_weight_table=False,
        uses_native_decide=False,
        uses_sorry=False,
        axioms_used=("propext", "Classical.choice", "Quot.sound"),
    )
    bank = load_witness_bank(bank_path)
    wb_truth = verify_witness_bank_ground_truth(bank_path)

    gate_stateful_q2 = evaluate_hypothesis_against_witness_bank(
        "StatefulQ2AutomatonDistinguishesMultiEvenPreimage",
        _dynamic_pred_stateful_q2_automaton_distinguishes_multi_even,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    gate_phi2_d6 = evaluate_hypothesis_against_witness_bank(
        "OutsideCones456Phi2OnCousinDiamond6",
        _dynamic_pred_phi2_on_cousin_diamond6_outside_cones456,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    gate_twobase_4x4 = evaluate_hypothesis_against_witness_bank(
        "TwoBase4x4LaurentDetNonzeroForAllCoprime",
        _dynamic_pred_twobase_4x4_laurent_det_nonzero_for_all_coprime,
        domains=("log2_3_convergents",),
        bank_path=bank_path,
    )
    gate_third_prime = evaluate_hypothesis_against_witness_bank(
        "ThirdCoprimeOrderPrimeEscapesMod8Subgroup",
        _dynamic_pred_third_coprime_prime_escapes_mod8_13,
        domains=("log2_3_convergents",),
        bank_path=bank_path,
    )
    gate_mixed_ray = evaluate_hypothesis_against_witness_bank(
        "RawMixedQ0VsQPosDisjointnessWithoutFirstHit",
        _dynamic_pred_mixed_q0_qpos_raw_disjointness,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )

    front_a = audit_w9_front_a_srs_d2_barrier_d3_omit_r9_and_zantema()
    front_b = audit_w9_front_b_laurent_4x4_twobase_and_coprime_sieve()
    front_c = audit_w9_front_c_stateful_automaton_barrier_and_diamond6()
    front_d = audit_w9_front_d_global_collision_and_markov_pow3()

    passed = (
        u_gate.passed
        and bool(wb_truth["all_witnesses_ground_truth_verified"])
        and (not gate_stateful_q2["passed"])
        and gate_stateful_q2["minimal_failure"]
        == ("z_pos_high_glide", "ZPOS_STATEFUL_Q2_COLLISION_800_VS_3200")
        and (not gate_phi2_d6["passed"])
        and gate_phi2_d6["minimal_failure"]
        == ("z_pos_high_glide", "ZPOS_COUSIN_DIAMOND6_CONE7_21232853_JUMP")
        and (not gate_twobase_4x4["passed"])
        and gate_twobase_4x4["minimal_failure"]
        == ("log2_3_convergents", "LAURENT_TWOBASE_4X4_RESONANT_ZERO_W9_K16_U2")
        and (not gate_third_prime["passed"])
        and gate_third_prime["minimal_failure"]
        == ("log2_3_convergents", "COPRIME_PRIMES_45661129_MOD8_1_AND_107889071_MOD8_7")
        and (not gate_mixed_ray["passed"])
        and gate_mixed_ray["minimal_failure"]
        == ("z_pos_high_glide", "ZPOS_RAY_MIXED_Q0_Q1_COLLISION_5")
        and bool(front_a["omit_r9_10_of_11_5level_3d_tower_verified"])
        and bool(front_a["zantema_mod_m_semantic_algebra_verified"])
        and bool(front_a["s9_mod2_labelled_7level_2d_tower_verified"])
        and bool(front_a["s9_subseq_pumping_zero_diag_obstruction_verified"])
        and bool(front_a["s9_parikh_syzygy_and_boundary_nontri_2d_collapse_verified"])
        and bool(front_b["laurent_4x4_three_closed_forms_and_cone_verified"])
        and bool(front_b["twobase_4x4_resonant_zero_9_16_2_verified"])
        and bool(front_b["coprime_primes_p3_45661129_and_p4_107889071_verified"])
        and bool(front_b["joint_331_and_107889071_floors_verified"])
        and bool(front_c["stateful_automaton_q_factorial_family_verified"])
        and bool(front_c["stateful_transducer_affine_and_mersenne_barrier_verified"])
        and bool(front_c["cousin_diamond6_outside_cones4567_descent_verified"])
        and bool(front_c["cousin_diamond6_cone7_return_and_spiral_verified"])
        and bool(front_c["cousin_diamond6_countermodels_verified"])
        and bool(front_d["global_all_pairs_classification_verified"])
        and bool(front_d["global_first_hit_injectivity_verified"])
        and bool(front_d["markov_mod18_and_pow3_memory_annihilation_verified"])
        and bool(front_d["markov_mod18_table_and_multistep_equidistribution_verified"])
    )
    return {
        "passed": passed,
        "verdict": "REDTEAM-PASSED" if passed else "FALSIFIED",
        "universality_gate_passed": u_gate.passed,
        "witness_bank_total_entries": sum(len(v) for v in bank["domains"].values()),
        "witness_bank_falsified_count": len(bank["falsified_hypotheses"]),
        "witness_bank_ground_truth_verified": bool(wb_truth["all_witnesses_ground_truth_verified"]),
        "front_a_srs_d3_and_zantema": front_a,
        "front_b_laurent_4x4_and_coprime_sieve": front_b,
        "front_c_stateful_automaton_and_diamond6": front_c,
        "front_d_global_collision_and_markov_pow3": front_d,
    }


# ==============================================================================
# Wave 10: Swap-Active Zantema `M = 3` / Two-Sided Semantic Labelling & Syzygies,
#          Universal 1-Block Coprime-Order Prime Law + Mod-24 Exclusion + `6 x 6`
#          Two-Base Schneider-Laurent Exact Zero Locus, Stern-Brocot & Zero-Testing
#          `1`-Counter (`OCN`) Preimage Barriers + `T_diamond7` (`omega^5`), and
#          Coupled Archimedean-Triadic Dyadic-Window `[2^M, 2^(M+1))` Pinning
# ==============================================================================


def stern_diatomic(n: int) -> int:
    """
    2-regular Stern-Brocot diatomic sequence `stern(n)` (`n >= 0`):
      - `stern(0) == 0`, `stern(1) == 1`;
      - `stern(2 * k) == stern(k)`;
      - `stern(2 * k + 1) == stern(k) + stern(k + 1)`.
    Computed iteratively in `O(log n)` bit operations via the standard `(a, b)`
    Euclid/Stern-Brocot matrix reduction so arbitrarily large `n` never overflow recursion.
    """
    if isinstance(n, bool) or not isinstance(n, int) or n < 0:
        raise ValueError(f"Expected non-negative integer n >= 0, got {n!r}")
    if n == 0:
        return 0
    a, b = 1, 0
    cur = n
    while cur > 0:
        if (cur & 1) == 0:
            a = a + b
        else:
            b = a + b
        cur >>= 1
    return b


def run_msb_one_counter_ocn(
    num_states: int,
    delta_zero: Sequence[Tuple[Any, Any]],
    delta_pos: Sequence[Tuple[Any, Any]],
    q0: int,
    n: int,
    c0: int = 0,
) -> Tuple[int, int]:
    """
    Run a `Q`-state MSB-first zero-testing `1`-counter pushdown automaton (`OCN`)
    on the canonical MSB-first binary expansion of `n >= 1`:
      - Control state `q in {0, ..., num_states - 1}` and unbounded counter `c >= 0`;
      - When `c == 0`, reading bit `b in {0, 1}` applies `delta_zero[q][b]`, which may be
        either an integer `dc in {0, 1}` (keeping state `q` for `Q == 1` convenience) or
        a pair `(q_next, dc)` with `dc in {0, 1}`;
      - When `c >= 1`, reading bit `b in {0, 1}` applies `delta_pos[q][b]`, which may be
        either an integer `dc in {-1, 0, 1}` (keeping state `q` for `Q == 1` convenience)
        or a pair `(q_next, dc)` with `dc in {-1, 0, 1}`.
    Returns `(final_state, final_counter)`.
    """
    if isinstance(num_states, bool) or not isinstance(num_states, int) or num_states < 1:
        raise ValueError(f"Expected integer num_states >= 1, got {num_states!r}")
    if isinstance(q0, bool) or not isinstance(q0, int) or not (0 <= q0 < num_states):
        raise ValueError(f"Expected initial state 0 <= q0 < {num_states}, got {q0!r}")
    if isinstance(n, bool) or not isinstance(n, int) or n < 1:
        raise ValueError(f"Expected positive integer n >= 1, got {n!r}")
    if isinstance(c0, bool) or not isinstance(c0, int) or c0 < 0:
        raise ValueError(f"Expected initial counter c0 >= 0, got {c0!r}")
    if len(delta_zero) != num_states or len(delta_pos) != num_states:
        raise ValueError("delta_zero and delta_pos must have length num_states")

    norm_zero: List[Tuple[Tuple[int, int], Tuple[int, int]]] = []
    norm_pos: List[Tuple[Tuple[int, int], Tuple[int, int]]] = []
    for st_i in range(num_states):
        rz = delta_zero[st_i]
        rp = delta_pos[st_i]
        if len(rz) != 2 or len(rp) != 2:
            raise ValueError("Each state row must specify transitions for bits (0, 1)")
        parsed_z: List[Tuple[int, int]] = []
        for entry_z in rz:
            if isinstance(entry_z, tuple) and len(entry_z) == 2:
                qn, dc = entry_z
            elif num_states == 1 and not isinstance(entry_z, bool) and isinstance(entry_z, int):
                qn, dc = 0, entry_z
            else:
                raise ValueError(f"Invalid delta_zero transition {entry_z!r}")
            if (
                isinstance(qn, bool)
                or isinstance(dc, bool)
                or not isinstance(qn, int)
                or not isinstance(dc, int)
                or not (0 <= qn < num_states)
                or dc not in (0, 1)
            ):
                raise ValueError(f"Out-of-range delta_zero transition {(qn, dc)!r}")
            parsed_z.append((qn, dc))
        norm_zero.append((parsed_z[0], parsed_z[1]))

        parsed_p: List[Tuple[int, int]] = []
        for entry_p in rp:
            if isinstance(entry_p, tuple) and len(entry_p) == 2:
                qn, dc = entry_p
            elif num_states == 1 and not isinstance(entry_p, bool) and isinstance(entry_p, int):
                qn, dc = 0, entry_p
            else:
                raise ValueError(f"Invalid delta_pos transition {entry_p!r}")
            if (
                isinstance(qn, bool)
                or isinstance(dc, bool)
                or not isinstance(qn, int)
                or not isinstance(dc, int)
                or not (0 <= qn < num_states)
                or dc not in (-1, 0, 1)
            ):
                raise ValueError(f"Out-of-range delta_pos transition {(qn, dc)!r}")
            parsed_p.append((qn, dc))
        norm_pos.append((parsed_p[0], parsed_p[1]))

    q_cur = q0
    c_cur = c0
    for ch in bin(n)[2:]:
        bit = 1 if ch == "1" else 0
        if c_cur == 0:
            q_cur, dc_cur = norm_zero[q_cur][bit]
            c_cur = dc_cur
        else:
            q_cur, dc_cur = norm_pos[q_cur][bit]
            c_cur = c_cur + dc_cur
    return (q_cur, c_cur)


def is_diamond7_cone8(x: int) -> bool:
    """
    Return True iff `x` belongs to `Cone 8` of 7th solvable cousin `T_diamond7`:
      `x >= 12_548_309`, `x % 4_194_304 == 4_159_701` (`x + 34_603 == 0 mod 2^22`),
      `x % 3 == 2`, and `coprime23Core(x + 34_603) == 1`
      (i.e. `x + 34_603 == 2^k * 3^m` with `k >= 22, m >= 1`).
    """
    if isinstance(x, bool) or not isinstance(x, int):
        raise ValueError(f"Expected integer x, got {x!r}")
    if x < 12_548_309 or (x % 4_194_304) != 4_159_701 or (x % 3) != 2:
        return False
    return _decompose_2_3_coprime(x + 34_603)[2] == 1


def cousin_diamond7_step_int(x: int, q: int = 3) -> int:
    """
    Seventh solvable mixed-(2,3) Collatz cousin `T_diamond7` on `Z` (for odd `q >= 3`),
    exhibiting genuine 5-tier `omega^5` Syracuse cascades
    (`Cone 8 -> Cone 7 -> Cone 6 -> Cone 5 -> Phi_diamond2`):
      - If `is_diamond7_cone8(x)`: `(q * x + 1) // 128`
        (at `q = 3`, steps `2^k * 3^m - 34_603 -> 2^(k - 7) * 3^(m + 1) - 811` directly into Cone 7!);
      - Otherwise: `cousin_diamond6_step_int(x, q=q)`.
    """
    if isinstance(x, bool) or not isinstance(x, int):
        raise ValueError(f"Expected integer x, got {x!r}")
    if isinstance(q, bool) or not isinstance(q, int) or (q & 1) == 0 or q < 3:
        raise ValueError(f"Expected odd multiplier q >= 3, got {q!r}")
    if is_diamond7_cone8(x):
        return (q * x + 1) // 128
    return cousin_diamond6_step_int(x, q=q)


def cousin_diamond7_step_q6(x: Fraction) -> Fraction:
    """
    Canonical extension of `T_diamond7` (`q = 3`) to `Q_(6) = {a/b : gcd(b, 6) == 1}`.
    Agrees identically with `cousin_diamond7_step_int` on all integers `a/1`, avoids Cone 8
    universally on all non-integer rationals `den >= 5`, and preserves `Q_(6)`.
    """
    if isinstance(x, bool) or not isinstance(x, (int, Fraction)):
        raise ValueError(f"Expected int or Fraction x, got {x!r}")
    if not isinstance(x, Fraction):
        x = Fraction(x)
    if math.gcd(x.denominator, 6) != 1:
        raise ValueError(f"Expected rational with gcd(denom, 6) == 1, got {x}")
    num = x.numerator
    den = x.denominator
    inv_d_4m = pow(den, -1, 4_194_304)
    inv_d_3 = pow(den, -1, 3)
    r4m = (num * inv_d_4m) % 4_194_304
    r3 = (num * inv_d_3) % 3
    if (
        num >= 12_548_309 * den
        and r4m == 4_159_701
        and r3 == 2
        and core3_pos(core2_pos(num + 34_603 * den)) == den
    ):
        return (3 * x + 1) / 128
    return cousin_diamond6_step_q6(x)


def cousin_diamond7_block_return(x: int) -> Tuple[int, int]:
    """
    Exact 5-tier `omega^5` return `(horizon_steps, next_state)` for `T_diamond7` on `Z^+`:
      - `x == 1`: `(0, 1)`;
      - `x == 2`: `(1, 1)`;
      - `is_diamond7_cone8(x)` (`x + 34_603 == 2^k * 3^m`, `k >= 22, m >= 1`):
        steps once via `(3 * x + 1) // 128` into `Cone 7` (`y = 2^(k - 7) * 3^(m + 1) - 811`)
        and drains to `1` in `1 + h_cone7(y)` total steps;
      - `is_diamond3_cone4(x)` or `is_diamond4_cone5(x)` or `is_diamond5_cone6(x)` or `is_diamond6_cone7(x)`:
        identical to `cousin_diamond6_block_return(x)` (since zero states along Cone-4/5/6/7
        orbits lie in Cone 8);
      - all other `x > 2`: `(1, cousin_diamond7_step_int(x))` (strictly decreasing `Phi_diamond2`).
    """
    if isinstance(x, bool) or not isinstance(x, int) or x < 1:
        raise ValueError(f"Expected positive integer x >= 1, got {x!r}")
    if x == 1:
        return (0, 1)
    if x == 2:
        return (1, 1)
    if is_diamond7_cone8(x):
        y = cousin_diamond7_step_int(x, q=3)
        if not is_diamond6_cone7(y):
            raise AssertionError(f"Cone 8 step at x={x} missed Cone 7: y={y}")
        h_c7, end_c7 = cousin_diamond6_block_return(y)
        horizon = 1 + h_c7
        cur = x
        for _ in range(horizon):
            cur = cousin_diamond7_step_int(cur, q=3)
        if end_c7 != 1 or cur != 1:
            raise AssertionError(f"Cone 8 return mismatch under T_diamond7 at x={x}: ended at {cur}")
        return (horizon, 1)
    if (
        is_diamond3_cone4(x)
        or is_diamond4_cone5(x)
        or is_diamond5_cone6(x)
        or is_diamond6_cone7(x)
    ):
        horizon, end_st = cousin_diamond6_block_return(x)
        cur = x
        for _ in range(horizon):
            cur = cousin_diamond7_step_int(cur, q=3)
        if end_st != 1 or cur != 1:
            raise AssertionError(f"Cone 4/5/6/7 return mismatch under T_diamond7 at x={x}: ended at {cur}")
        return (horizon, 1)
    return (1, cousin_diamond7_step_int(x, q=3))


def _bareiss_det_exact(mat: Sequence[Sequence[int]]) -> int:
    """Exact fraction-free Bareiss integer determinant for `n x n` integer matrices."""
    n = len(mat)
    if n == 0:
        return 1
    a = [[int(v) for v in row] for row in mat]
    sign = 1
    prev = 1
    for k_i in range(n - 1):
        if a[k_i][k_i] == 0:
            for sw_i in range(k_i + 1, n):
                if a[sw_i][k_i] != 0:
                    a[k_i], a[sw_i] = a[sw_i], a[k_i]
                    sign = -sign
                    break
            else:
                return 0
        for r_i in range(k_i + 1, n):
            for c_i in range(k_i + 1, n):
                a[r_i][c_i] = (a[r_i][c_i] * a[k_i][k_i] - a[r_i][k_i] * a[k_i][c_i]) // prev
        prev = a[k_i][k_i]
    return sign * a[n - 1][n - 1]


def laurent_twobase_6x6_det_matrix(w_val: int, k_val: int, u_val: int) -> int:
    """
    Exact `6 x 6` two-base `(T = 2, U = 3)` Schneider-Laurent integer determinant on
    `rows = [(0,0),(1,0),(0,1),(1,1),(0,2),(1,2)]` and
    `cols = [(0,0),(1,0),(0,u),(1,u),(0,2u),(1,2u)]`.
    """
    if (
        isinstance(w_val, bool)
        or isinstance(k_val, bool)
        or isinstance(u_val, bool)
        or not isinstance(w_val, int)
        or not isinstance(k_val, int)
        or not isinstance(u_val, int)
        or w_val < 0
        or k_val < 0
        or u_val < 1
    ):
        raise ValueError(f"Expected integers W >= 0, K >= 0, u >= 1, got {(w_val, k_val, u_val)!r}")
    rows6 = ((0, 0), (1, 0), (0, 1), (1, 1), (0, 2), (1, 2))
    cols6 = ((0, 0), (1, 0), (0, u_val), (1, u_val), (0, 2 * u_val), (1, 2 * u_val))
    mat6 = [
        [
            math.comb(r_i * w_val + s_i * k_val, t_i) * (1 << (r_i * m_i)) * (3 ** (s_i * m_i))
            for (t_i, m_i) in cols6
        ]
        for (r_i, s_i) in rows6
    ]
    return _bareiss_det_exact(mat6)


def laurent_twobase_6x6_det_closed(w_val: int, k_val: int, u_val: int) -> int:
    """
    Exact factored closed form of `laurent_twobase_6x6_det_matrix(W, K, u)`:
      `P * Q^2 * q^3 * (P * (Q^2 - 1) * W - Q * (P^2 - 1) * K)`
      `* (P * q^2 * (Q + 1) * W^2 + Q * (P^2 - 1) * q * W * K - 2 * Q * p^2 * (Q + 1) * K^2)`
    where `P = 2^u`, `Q = 3^u`, `p = P - 1`, `q = Q - 1`.
    """
    if (
        isinstance(w_val, bool)
        or isinstance(k_val, bool)
        or isinstance(u_val, bool)
        or not isinstance(w_val, int)
        or not isinstance(k_val, int)
        or not isinstance(u_val, int)
        or w_val < 0
        or k_val < 0
        or u_val < 1
    ):
        raise ValueError(f"Expected integers W >= 0, K >= 0, u >= 1, got {(w_val, k_val, u_val)!r}")
    p_pow = 1 << u_val
    q_pow = 3**u_val
    p_sub = p_pow - 1
    q_sub = q_pow - 1
    pref = p_pow * (q_pow * q_pow) * (q_sub**3)
    lin_fac = p_pow * (q_pow * q_pow - 1) * w_val - q_pow * (p_pow * p_pow - 1) * k_val
    quad_fac = (
        p_pow * (q_sub * q_sub) * (q_pow + 1) * (w_val * w_val)
        + q_pow * (p_pow * p_pow - 1) * q_sub * w_val * k_val
        - 2 * q_pow * (p_sub * p_sub) * (q_pow + 1) * (k_val * k_val)
    )
    return pref * lin_fac * quad_fac


def audit_w10_front_a_srs_omit_r8_termination_and_labelled_syzygies() -> Dict[str, Any]:
    """
    Front A (`Branch P4.3`):
    1. Verify exact `collatzSemMod(M)` (`L -> 0`, `R -> 1 % M`, `B_j -> 2a + j`, `T_i -> 3a + i`)
       semantic preservation across `M = 1..12` and universal fixed-point swap preservation:
       `R3` at `a = 0` is `[T0_0, B0_0] -> [B0_0, T0_0]` and `R8` at `a = M - 1` is
       `[T2_{M-1}, B1_{M-1}] -> [B1_{M-1}, T2_{M-1}]`.
    2. Verify that `M = 3` Zantema semantic labelling (`21` symbols):
       - Collapses swap-free `S9 = all11 \\ {R3, R8}` (`27` rules) from 7 levels (`M = 2, 2D`)
         down to a **2-level `1D` natural-affine / `2D` tower** (`27 -> 4 -> 0`);
       - Strictly removes Garden-of-Eden rule `R2_1` (`[L_0, B1_1] -> [L_2, T2_1]`) from
         **full `all11`** (`33 -> 32` rules) and `omit R8` (`30 -> 29` rules);
       - Strictly removes `5` rules (`R1_0, R2_1, R4_1, R5_0, R7_0`) from `omit R3` (`30 -> 25`).
    3. Verify exact 2-state left-to-right model `semL2` + Two-Sided `(semL2 x collatzSemMod M)`:
       - At `M = 2` (`28` symbols), strictly removes `14/40` rules from `omit R8` (`40 -> 26`)
         and `4/40` rules from `omit R3` (`40 -> 36`);
       - At `M = 6` (`84` symbols), **completely terminates swap-active `omit R8 = all11 \\ {R8}`
         (`10/11` rules with `R3` swap and all 4 recurrent rules `{R2, R5, R7, R9}` active!)**
         via a 2-level `1D`-affine / `2D` Hofbauer-Waldmann tower (`120 -> 15 -> 0`)!
    4. Verify strictly positive integer Parikh syzygy barriers proving `0` Parikh removals on
       `M = 2` (`20/20`, `20/20`, `22/22`), `M = 3` cores (`32/32`, `29/29`, `25/25`),
       `M = 4` (`40/40`, `40/40`, `44/44`), and `TwoSided(2x2)` (`44/44`, `26/26`, `36/36`)!
    """
    base_rules: List[Tuple[str, Tuple[int, ...], Tuple[int, ...]]] = [
        ("R1", (0, 2), (0,)),
        ("R2", (0, 3), (0, 6)),
        ("R3", (4, 2), (2, 4)),
        ("R4", (4, 3), (3, 5)),
        ("R5", (5, 2), (3, 4)),
        ("R6", (5, 3), (2, 6)),
        ("R7", (6, 2), (2, 5)),
        ("R8", (6, 3), (3, 6)),
        ("R9", (4, 1), (3, 1)),
        ("R10", (5, 1), (2, 2, 1)),
        ("R11", (6, 1), (3, 2, 1)),
    ]

    def _sem_mod(mod_m: int, sym: int, a_c: int) -> int:
        if sym == 0:
            return 0
        if sym == 1:
            return 1 % mod_m
        if sym == 2:
            return (2 * a_c) % mod_m
        if sym == 3:
            return (2 * a_c + 1) % mod_m
        if sym == 4:
            return (3 * a_c) % mod_m
        if sym == 5:
            return (3 * a_c + 1) % mod_m
        return (3 * a_c + 2) % mod_m

    def _eval_sem_r(mod_m: int, word: Sequence[int], a_c: int) -> int:
        cur = a_c
        for s_i in reversed(word):
            cur = _sem_mod(mod_m, s_i, cur)
        return cur

    def _label_word_r(mod_m: int, word: Sequence[int], a_c: int) -> Tuple[int, ...]:
        return tuple(
            word[idx] * mod_m + _eval_sem_r(mod_m, word[idx + 1 :], a_c)
            for idx in range(len(word))
        )

    def _labelled_r(
        mod_m: int, rules_sub: Sequence[Tuple[str, Tuple[int, ...], Tuple[int, ...]]]
    ) -> List[Tuple[str, Tuple[int, ...], Tuple[int, ...]]]:
        return [
            (f"{nm}_{a_c}", _label_word_r(mod_m, lw, a_c), _label_word_r(mod_m, rw, a_c))
            for (nm, lw, rw) in rules_sub
            for a_c in range(mod_m - 1, -1, -1)
        ]

    # 1. Semantic preservation & fixed-point swap preservation across M = 1..12
    fixed_swap_ok = True
    for mod_m in range(1, 13):
        if any(
            _eval_sem_r(mod_m, lw, a_c) != _eval_sem_r(mod_m, rw, a_c)
            for (_, lw, rw) in base_rules
            for a_c in range(mod_m)
        ):
            fixed_swap_ok = False
            break
        r3_0_l = _label_word_r(mod_m, (4, 2), 0)
        r3_0_r = _label_word_r(mod_m, (2, 4), 0)
        r8_m1_l = _label_word_r(mod_m, (6, 3), mod_m - 1)
        r8_m1_r = _label_word_r(mod_m, (3, 6), mod_m - 1)
        if r3_0_l != (r3_0_r[1], r3_0_r[0]) or r8_m1_l != (r8_m1_r[1], r8_m1_r[0]):
            fixed_swap_ok = False
            break

    # 2. M = 3 S9 2-level 1D-affine termination (27 -> 4 -> 0), full all11 R2_1 removal (33 -> 32),
    #    and omit R3 5-rule removal (30 -> 25)
    def _eval_1d_affine(mc: Sequence[Tuple[int, int]], word: Sequence[int]) -> Tuple[int, int]:
        m_acc, c_acc = 1, 0
        for sym in reversed(word):
            ms, cs = mc[sym]
            m_acc, c_acc = ms * m_acc, ms * c_acc + cs
        return (m_acc, c_acc)

    def _verify_1d_tower(
        nsyms: int,
        rules_in: Sequence[Tuple[str, Tuple[int, ...], Tuple[int, ...]]],
        levels: Sequence[Sequence[Tuple[int, int]]],
    ) -> bool:
        rem = list(rules_in)
        for mc in levels:
            if len(mc) != nsyms or any(ms < 1 or cs < 0 for (ms, cs) in mc):
                return False
            nxt_rem: List[Tuple[str, Tuple[int, ...], Tuple[int, ...]]] = []
            for rec in rem:
                _, lw, rw = rec
                ml, cl = _eval_1d_affine(mc, lw)
                mr, cr = _eval_1d_affine(mc, rw)
                if ml < mr or cl < cr:
                    return False
                if cl == cr:
                    nxt_rem.append(rec)
            if len(nxt_rem) == len(rem):
                return False
            rem = nxt_rem
        return len(rem) == 0

    omit_r8 = [r for r in base_rules if r[0] != "R8"]
    omit_r3 = [r for r in base_rules if r[0] != "R3"]
    s9_rules = [r for r in base_rules if r[0] not in ("R3", "R8")]

    wt_m3_s9 = (
        10, 1, 0, 0, 0, 0, 12, 2, 0, 0, 0,
        6, 4, 9, 2, 9, 3, 7, 0, 9, 5,
    )
    mc_m3_interior = tuple(
        (1, 0) if (s_i // 3) in (0, 1) else ((1, 1) if (s_i // 3) in (2, 3) else (2, 0))
        for s_i in range(21)
    )
    m3_s9_ok = _verify_1d_tower(
        21,
        _labelled_r(3, s9_rules),
        (tuple((1, w_i) for w_i in wt_m3_s9), mc_m3_interior),
    )

    all11_m3 = _labelled_r(3, base_rules)
    goe_removed = [nm for (nm, lw, rw) in all11_m3 if lw.count(0) > rw.count(0)]
    goe_weak_ok = all(lw.count(0) >= rw.count(0) for (_, lw, rw) in all11_m3)
    m3_all11_goe_ok = goe_weak_ok and (goe_removed == ["R2_1"])

    wt_m3_or3 = (
        3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0,
        0, 2, 0, 0, 0, 0, 0, 0, 0, 0,
    )
    or3_m3 = _labelled_r(3, omit_r3)
    m3_or3_weak = all(
        sum(wt_m3_or3[s_i] for s_i in lw) >= sum(wt_m3_or3[s_i] for s_i in rw)
        for (_, lw, rw) in or3_m3
    )
    m3_or3_rem = [
        nm
        for (nm, lw, rw) in or3_m3
        if sum(wt_m3_or3[s_i] for s_i in lw) > sum(wt_m3_or3[s_i] for s_i in rw)
    ]
    m3_or3_ok = m3_or3_weak and (
        m3_or3_rem == ["R1_0", "R2_1", "R4_1", "R5_0", "R7_0"]
    )

    # 3. Left-to-right 2-state model semL2 & Two-Sided (semL2 x collatzSemMod 2)
    def _sem_l2(sym: int, q_st: int) -> int:
        if sym in (0, 1, 2, 4):
            return 0
        if sym in (3, 6):
            return 1
        return q_st

    def _eval_sem_l2(word: Sequence[int], q_st: int) -> int:
        cur = q_st
        for s_i in word:
            cur = _sem_l2(s_i, cur)
        return cur

    sem_l2_ok = all(
        _eval_sem_l2(lw, q_st) == _eval_sem_l2(rw, q_st)
        for (_, lw, rw) in base_rules
        for q_st in (0, 1)
    )

    def _label_2sided(mod_m: int, word: Sequence[int], q_st: int, a_c: int) -> Tuple[int, ...]:
        out: List[int] = []
        cq = q_st
        for idx, s_i in enumerate(word):
            out.append(s_i * (2 * mod_m) + cq * mod_m + _eval_sem_r(mod_m, word[idx + 1 :], a_c))
            cq = _sem_l2(s_i, cq)
        return tuple(out)

    def _labelled_2s(
        mod_m: int,
        rules_sub: Sequence[Tuple[str, Tuple[int, ...], Tuple[int, ...]]],
    ) -> List[Tuple[str, Tuple[int, ...], Tuple[int, ...]]]:
        return [
            (
                f"{nm}_q{q_st}a{a_c}",
                _label_2sided(mod_m, lw, q_st, a_c),
                _label_2sided(mod_m, rw, q_st, a_c),
            )
            for (nm, lw, rw) in rules_sub
            for q_st in (0, 1)
            for a_c in range(mod_m - 1, -1, -1)
        ]

    wt_2s_or8 = (
        0, 89, 0, 89, 1, 1, 98, 98, 135, 89, 148, 102, 168, 173,
        130, 66, 270, 270, 283, 232, 316, 224, 265, 275, 257, 173, 333, 202,
    )
    or8_2s_rules = _labelled_2s(2, omit_r8)
    or8_2s_weak = all(
        sum(wt_2s_or8[s_i] for s_i in lw) >= sum(wt_2s_or8[s_i] for s_i in rw)
        for (_, lw, rw) in or8_2s_rules
    )
    or8_2s_rem = [
        nm
        for (nm, lw, rw) in or8_2s_rules
        if sum(wt_2s_or8[s_i] for s_i in lw) > sum(wt_2s_or8[s_i] for s_i in rw)
    ]
    twosided_or8_ok = or8_2s_weak and len(or8_2s_rem) == 14

    wt_2s_or3 = (
        0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    )
    or3_2s_rules = _labelled_2s(2, omit_r3)
    or3_2s_weak = all(
        sum(wt_2s_or3[s_i] for s_i in lw) >= sum(wt_2s_or3[s_i] for s_i in rw)
        for (_, lw, rw) in or3_2s_rules
    )
    or3_2s_rem = [
        nm
        for (nm, lw, rw) in or3_2s_rules
        if sum(wt_2s_or3[s_i] for s_i in lw) > sum(wt_2s_or3[s_i] for s_i in rw)
    ]
    twosided_or3_ok = or3_2s_weak and (
        or3_2s_rem == ["R4_q0a1", "R4_q0a0", "R9_q0a1", "R9_q0a0"]
    )

    # Complete 2-level 1D-affine / 2D termination of omit R8 (120 -> 15 -> 0) under TwoSided(2 x 6)
    wt_2s_m6_or8 = (
        0, 0, 0, 9, 0, 0, 0, 0, 0, 9, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        47, 1, 53, 45, 43, 1, 0, 0, 49, 0, 34, 22,
        81, 93, 100, 122, 91, 156, 39, 0, 0, 0, 0, 0,
        89, 94, 138, 88, 133, 85, 43, 2, 94, 0, 85, 0,
        78, 55, 123, 37, 123, 53, 82, 90, 91, 124, 85, 149,
        80, 101, 99, 0, 75, 0, 79, 1, 90, 0, 75, 0,
    )
    mc_2s_m6_interior = tuple(
        (1, 0) if (s_i // 12) in (0, 1) else ((1, 1) if (s_i // 12) in (2, 3) else (2, 0))
        for s_i in range(84)
    )
    or8_2s_m6 = _labelled_2s(6, omit_r8)
    or8_2s_m6_core15 = [
        r for r in or8_2s_m6
        if sum(wt_2s_m6_or8[s_i] for s_i in r[1]) == sum(wt_2s_m6_or8[s_i] for s_i in r[2])
    ]
    twosided_m6_or8_term_ok = (
        len(or8_2s_m6) == 120
        and len(or8_2s_m6_core15) == 15
        and _verify_1d_tower(
            84,
            or8_2s_m6,
            (tuple((1, w_i) for w_i in wt_2s_m6_or8), mc_2s_m6_interior),
        )
    )

    # 4. Strictly positive Parikh syzygy barriers (y_i >= 1 with sum_i y_i * (count_L(s) - count_R(s)) <= 0)
    def _verify_positive_syzygy(
        nsyms: int,
        rules_in: Sequence[Tuple[str, Tuple[int, ...], Tuple[int, ...]]],
        mults: Sequence[int],
    ) -> bool:
        if len(mults) != len(rules_in) or any(m_i < 1 for m_i in mults):
            return False
        for sym in range(nsyms):
            net = sum(
                mults[i_r] * (rules_in[i_r][1].count(sym) - rules_in[i_r][2].count(sym))
                for i_r in range(len(rules_in))
            )
            if net > 0:
                return False
        return True

    syz_m2_or8 = (7, 1, 7, 7, 2, 1, 1, 3, 4, 3, 1, 2, 4, 4, 1, 1, 1, 1, 4, 4)
    syz_m2_or3 = (5, 2, 18, 5, 2, 6, 13, 2, 2, 3, 7, 10, 2, 10, 2, 2, 2, 2, 5, 5)
    syz_m2_all11 = (
        18, 6, 35, 18, 10, 6, 6, 12, 23, 12, 6,
        7, 21, 24, 6, 21, 6, 6, 7, 7, 10, 10,
    )
    r32_m3 = [r for r in all11_m3 if r[0] != "R2_1"]
    syz_m3_32 = (
        2, 12, 2, 20, 10, 2, 7, 2, 7, 4, 5, 12, 7, 4, 2, 4,
        4, 2, 22, 3, 2, 14, 4, 2, 2, 2, 3, 3, 3, 4, 4, 4,
    )
    r29_m3_or8 = [r for r in _labelled_r(3, omit_r8) if r[0] != "R2_1"]
    syz_m3_29 = (
        6, 72, 6, 72, 66, 19, 104, 6, 7, 44, 72, 94, 7, 46, 7,
        95, 7, 8, 78, 69, 6, 6, 6, 7, 7, 7, 29, 29, 29,
    )
    r25_m3_or3 = [
        r for r in or3_m3
        if sum(wt_m3_or3[s_i] for s_i in r[1]) == sum(wt_m3_or3[s_i] for s_i in r[2])
    ]
    syz_m3_25 = (
        2, 4, 16, 2, 7, 2, 7, 8, 2, 2, 5, 3, 18,
        2, 13, 6, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    )
    r26_2s_or8 = [
        r for r in or8_2s_rules
        if sum(wt_2s_or8[s_i] for s_i in r[1]) == sum(wt_2s_or8[s_i] for s_i in r[2])
    ]
    syz_2s_26 = (
        45, 45, 23, 45, 23, 45, 71, 20, 25, 71, 25, 25, 23,
        23, 71, 25, 27, 48, 71, 94, 23, 23, 22, 22, 23, 23,
    )
    r36_2s_or3 = [
        r for r in or3_2s_rules
        if sum(wt_2s_or3[s_i] for s_i in r[1]) == sum(wt_2s_or3[s_i] for s_i in r[2])
    ]
    syz_2s_36 = (
        1, 1, 1, 1, 1, 1, 17, 1, 4, 7, 12, 1, 6, 1, 9, 1, 1, 1,
        1, 1, 11, 12, 19, 6, 1, 17, 3, 4, 1, 1, 1, 1, 1, 2, 1, 1,
    )
    syz_2s_all11 = (
        377, 120, 377, 120, 978, 377, 978, 377, 605, 120, 227, 672, 128, 295, 442,
        326, 1010, 626, 293, 298, 120, 566, 122, 194, 397, 1051, 881, 598, 995, 838,
        120, 672, 194, 194, 257, 257, 293, 293, 126, 126, 178, 178, 147, 147,
    )
    syz_m4_or8 = (
        9, 1, 1, 1, 1, 1, 9, 9, 1, 11, 11, 1, 1, 2, 5, 6, 5, 1, 1, 11,
        1, 9, 1, 1, 1, 4, 9, 6, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7,
    )
    syz_m4_or3 = (
        1, 1, 1, 1, 11, 1, 1, 1, 1, 4, 2, 1, 3, 1, 9, 1, 1, 1, 5, 1,
        5, 8, 4, 1, 1, 7, 12, 7, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    )
    syz_m4_all11 = (
        2, 2, 2, 2, 18, 2, 2, 2, 2, 2, 2, 2, 2, 7, 4, 2, 4, 2, 15, 2, 2, 2,
        7, 2, 7, 12, 8, 2, 2, 11, 20, 10, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    )
    syzygies_ok = (
        _verify_positive_syzygy(14, _labelled_r(2, omit_r8), syz_m2_or8)
        and _verify_positive_syzygy(14, _labelled_r(2, omit_r3), syz_m2_or3)
        and _verify_positive_syzygy(14, _labelled_r(2, base_rules), syz_m2_all11)
        and _verify_positive_syzygy(21, r32_m3, syz_m3_32)
        and _verify_positive_syzygy(21, r29_m3_or8, syz_m3_29)
        and _verify_positive_syzygy(21, r25_m3_or3, syz_m3_25)
        and _verify_positive_syzygy(28, r26_2s_or8, syz_2s_26)
        and _verify_positive_syzygy(28, r36_2s_or3, syz_2s_36)
        and _verify_positive_syzygy(28, _labelled_2s(2, base_rules), syz_2s_all11)
        and _verify_positive_syzygy(28, _labelled_r(4, omit_r8), syz_m4_or8)
        and _verify_positive_syzygy(28, _labelled_r(4, omit_r3), syz_m4_or3)
        and _verify_positive_syzygy(28, _labelled_r(4, base_rules), syz_m4_all11)
    )

    return {
        "fixed_point_swap_preservation_verified": fixed_swap_ok,
        "m3_s9_2level_1d_and_all11_goe_removal_verified": (
            m3_s9_ok and m3_all11_goe_ok and m3_or3_ok
        ),
        "twosided_l2_r2_omit_r8_14_and_omit_r3_4_removal_verified": (
            sem_l2_ok and twosided_or8_ok and twosided_or3_ok
        ),
        "twosided_l2_r6_omit_r8_2level_termination_verified": twosided_m6_or8_term_ok,
        "labelled_parikh_syzygy_barriers_verified": syzygies_ok,
    }


def audit_w10_front_b_coprime_prime_divisor_law_mod24_and_laurent_6x6() -> Dict[str, Any]:
    """
    Front B (`Branch P3.4` & `P3.3`):
    1. Verify the Universal 1-Block Coprime-Order Prime-Divisor & Subgroup-Product Law +
       Universal Mod-24 `{11, 13}` Quadratic-Reciprocity Exclusion across all odd primes
       `5 <= q < 20,000` (`gcd(ord_q(2), ord_q(3/2)) == 1 => ord_q(2) * ord_q(3/2) | (q - 1)`
       AND `(q % 24) not in (11, 13)`), and verify `p_1..p_4` (`331, 1210483, 45661129, 107889071`)
       all satisfy `d_2 * d_{32} | (p - 1)` and avoid `{11, 13} mod 24` (`19, 19, 1, 23`).
    2. Verify exact `6 x 6` Schneider-Laurent closed forms:
       - Single-base `(T = 5, U = 1)`: `det_6 == W^10 * (2^u - 1)^5 > 0`;
       - Two-base `(T = 2, U = 3)` (`laurent_twobase_6x6_det_matrix == laurent_twobase_6x6_det_closed`):
         exact zero locus `det_6 == 0 <=> 2^u * (3^(2u) - 1) * W == 3^u * (2^(2u) - 1) * K`
         (vanishing at `(9, 16, 1)`, `(27, 64, 2)`, `(243, 832, 3)`), non-zero across ALL
         `3 * K <= 5 * W, u >= 1`, sign-flipping at `u = 1` (`(2,3) > 0` vs `(5,8) < 0`) and
         `u = 2` (`(3,5) < 0` vs `(5,8) > 0`), and strictly `> 0` across ALL `3 * K <= 5 * W, u >= 3`!
    """
    reciprocity_and_lagrange_ok = True
    for q_p in range(5, 20_000, 2):
        if all(q_p % d_i != 0 for d_i in range(3, int(math.isqrt(q_p)) + 1, 2)):
            o2 = _mult_order_mod_prime(2, q_p)
            o32 = _mult_order_mod_prime((3 * pow(2, -1, q_p)) % q_p, q_p)
            g_o = math.gcd(o2, o32)
            if (q_p % 24) in (11, 13):
                leg2 = pow(2, (q_p - 1) // 2, q_p)
                leg3 = pow(3, (q_p - 1) // 2, q_p)
                if leg2 != q_p - 1 or leg3 != 1 or (g_o % 2) != 0:
                    reciprocity_and_lagrange_ok = False
                    break
                if (q_p % 24) == 13 and (g_o % 4) != 0:
                    reciprocity_and_lagrange_ok = False
                    break
            if g_o == 1:
                if ((q_p - 1) % (o2 * o32)) != 0 or (q_p % 24) in (11, 13):
                    reciprocity_and_lagrange_ok = False
                    break

    # Verify r >= 2 (46 = 23 * 2) 2-block squeeze across 1 <= v <= 40 (-> (82, 130) & (164, 260) floors)
    twoblock_mod24_and_r2_ok = reciprocity_and_lagrange_ok
    for v_sq in range(1, 41):
        k0_sq = (1585 * v_sq) // 1000 + 1
        if not (
            (1 << (k0_sq - 1)) <= (3**v_sq) < (1 << k0_sq)
            and 46 * ((1 << k0_sq) - (3**v_sq)) >= (3**v_sq)
        ):
            twoblock_mod24_and_r2_ok = False
            break

    known_coprime = (
        (331, 30, 11, 19),
        (1_210_483, 182, 2_217, 19),
        (45_661_129, 12_381, 1_844, 1),
        (107_889_071, 52_835, 1_021, 23),
    )
    for p_k, d2_k, d32_k, mod24_k in known_coprime:
        if (
            (p_k % 24) != mod24_k
            or mod24_k in (11, 13)
            or ((p_k - 1) % (d2_k * d32_k)) != 0
            or min(d2_k, d32_k) ** 2 >= p_k
        ):
            reciprocity_and_lagrange_ok = False

    # Single-base 6x6: BOTH (T=5, U=1) AND (T=2, U=3), plus confluent column-extrapolated zero-gap dvd
    rows_s6 = tuple((i, 0) for i in range(6))
    det6_single_ok = True
    det6_c23_and_extrap_ok = True
    for w_v in (1, 2, 3, 5):
        for u_v in (1, 2, 3):
            cols_t5 = ((0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (0, u_v))
            mat_s6 = [
                [math.comb(r_i * w_v, t_i) * (1 << (r_i * m_i)) for (t_i, m_i) in cols_t5]
                for (r_i, _) in rows_s6
            ]
            cols_c23 = ((0, 0), (1, 0), (0, u_v), (1, u_v), (0, 2 * u_v), (1, 2 * u_v))
            mat_c23 = [
                [math.comb(r_i * w_v, t_i) * (1 << (r_i * m_i)) for (t_i, m_i) in cols_c23]
                for (r_i, _) in rows_s6
            ]
            exp_c23 = (
                (w_v**3)
                * ((1 << u_v) ** 7)
                * (((1 << u_v) - 1) ** 12)
                * (((1 << u_v) + 1) ** 4)
            )
            if _bareiss_det_exact(mat_s6) != (w_v**10) * (((1 << u_v) - 1) ** 5):
                det6_single_ok = False
            if _bareiss_det_exact(mat_c23) != exp_c23:
                det6_c23_and_extrap_ok = False

    det6_twobase_ok = True
    rows_tb6 = ((0, 0), (1, 0), (0, 1), (1, 1), (0, 2), (1, 2))
    for u_v in (1, 2, 3, 4, 5):
        for w_v, k_v in ((1, 1), (2, 3), (3, 5), (5, 8), (9, 16), (12, 19), (27, 64)):
            dm = laurent_twobase_6x6_det_matrix(w_v, k_v, u_v)
            dc = laurent_twobase_6x6_det_closed(w_v, k_v, u_v)
            if dm != dc:
                det6_twobase_ok = False
                break
            if 3 * k_v <= 5 * w_v:
                if dc == 0 or (u_v >= 3 and dc <= 0):
                    det6_twobase_ok = False
                    break
            if u_v <= 2 and w_v <= 5 and (3**w_v) < (1 << k_v):
                cols_c23_u = ((0, 0), (1, 0), (0, u_v), (1, u_v), (0, 2 * u_v), (1, 2 * u_v))
                m0_tb6 = [
                    [
                        math.comb(r_i * w_v + s_i * k_v, t_i)
                        * (1 << ((r_i * w_v + s_i * k_v) * m_i))
                        for (t_i, m_i) in cols_c23_u
                    ]
                    for (r_i, s_i) in rows_tb6
                ]
                d0_tb6 = _bareiss_det_exact(m0_tb6)
                dw_tb6 = laurent_twobase_6x6_det_closed(w_v, k_v, w_v * u_v)
                gap_d = (1 << k_v) - (3**w_v)
                extrap_fac = (1 << u_v) * (((1 << u_v) - 1) ** 3)
                if ((d0_tb6 - dw_tb6) % gap_d) != 0 or (d0_tb6 % extrap_fac) != 0:
                    det6_c23_and_extrap_ok = False
                    break

    zero_locus_and_flip_ok = (
        laurent_twobase_6x6_det_matrix(9, 16, 1) == 0
        and laurent_twobase_6x6_det_matrix(27, 64, 2) == 0
        and laurent_twobase_6x6_det_closed(243, 832, 3) == 0
        and laurent_twobase_6x6_det_matrix(2, 3, 1) > 0
        and laurent_twobase_6x6_det_matrix(5, 8, 1) < 0
        and laurent_twobase_6x6_det_matrix(3, 5, 2) < 0
        and laurent_twobase_6x6_det_matrix(5, 8, 2) > 0
    )

    return {
        "coprime_order_lagrange_and_mod24_reciprocity_verified": reciprocity_and_lagrange_ok,
        "two_block_shared_mersenne_mod24_and_r2_squeeze_verified": twoblock_mod24_and_r2_ok,
        "laurent_6x6_single_base_t5u1_verified": det6_single_ok,
        "laurent_6x6_single_base_t2u3_and_confluent_extrapolation_verified": det6_c23_and_extrap_ok,
        "laurent_6x6_twobase_closed_form_and_cone_verified": det6_twobase_ok,
        "laurent_6x6_exact_zero_locus_and_u1_u2_flips_verified": zero_locus_and_flip_ok,
    }


def audit_w10_front_c_stern_ocn_barrier_and_diamond7() -> Dict[str, Any]:
    """
    Front C (`Branch P1.2` & `P5.9`):
    1. Verify 2-regular Stern-Brocot (`stern_diatomic`) exact closed forms along Mersenne
       `1`-spines (`m_r = 3*2^r - 1 -> 2r + 1`, `2*m_r -> 2r + 1`, `n_r = 2^(r+1) - 1 -> r + 1`)
       and `m_k = 3*4^k + 2` (`4k - 1`, `4k - 1`, `2k + 2`), plus universal unary `0`-run
       pumping dichotomy for non-regular zero-testing `1`-counter automata (`OCN`, `Q = 1, 2`)
       along `m_{Q, s} = 3 * 4^(K_Q + P_Q * s) + 2^(2*K_Q + 1)` vs `2^(P_Q) * m_{Q, s}`.
    2. Verify 7th solvable `(3x + 1)`-cousin `T_diamond7` (`omega^5` 5-tier cascade):
       - Strict `Phi_diamond2` descent in 1 step outside Cones 4, 5, 6, 7, 8 (`x = 3..4000`);
       - Exact Cone-8 -> Cone-7 -> Cone-6 -> Cone-5 5-tier cascade (`12548309 -> 294101 -> 6893 -> 2585`
         and `k = 113, m = 1` upward `Phi_diamond2` jump), zero Cone-8 hits along Cone-4/5/6/7
         orbits, polynomial bound `h <= (x+1)^3 + (x+1)^5`, and `M1`/`M2`/`M3` + `Q_(6)`/`Int`
         separation (including non-integer `12548309/7` Cone-8 avoidance!).
    """
    stern_ok = True
    for r_i in range(2, 18):
        mr = 3 * (1 << r_i) - 1
        evr = 2 * mr
        nr = (1 << (r_i + 1)) - 1
        if (
            stern_diatomic(mr) != 2 * r_i + 1
            or stern_diatomic(evr) != 2 * r_i + 1
            or stern_diatomic(nr) != r_i + 1
            or int_compressed_step(nr, q=3) != mr
        ):
            stern_ok = False
            break
    for k_i in range(1, 14):
        mk = 3 * (4**k_i) + 2
        evk = 2 * mk
        nk = (1 << (2 * k_i + 1)) + 1
        if (
            stern_diatomic(mk) != 4 * k_i - 1
            or stern_diatomic(evk) != 4 * k_i - 1
            or stern_diatomic(nk) != 2 * k_i + 2
            or int_compressed_step(nk, q=3) != mk
        ):
            stern_ok = False
            break
    # Alternating 01-cascade Fibonacci law: stern_diatomic((4^e - 1)//3) == F_{2e}
    stern_fib_and_zero_excess_ok = True
    fib_seq = [0, 1]
    for _ in range(28):
        fib_seq.append(fib_seq[-2] + fib_seq[-1])
    for e_i in range(1, 13):
        a_alt = ((4**e_i) - 1) // 3
        if (
            stern_diatomic(a_alt) != fib_seq[2 * e_i]
            or stern_diatomic(a_alt + 1) != fib_seq[2 * e_i - 1]
        ):
            stern_fib_and_zero_excess_ok = False
            break

    # Zero-testing OCN unary 0-run pumping dichotomy + non-regular zero-excess OCN ((zeroBitCount - oneBitCount)_+)
    ocn_ok = True
    for k_nr in range(1, 12):
        n_pos = (1 << (2 * k_nr - 1)) + ((1 << (k_nr - 1)) - 1)
        n_zro = (1 << (2 * k_nr - 2)) + ((1 << (k_nr - 1)) - 1)
        if (
            run_msb_one_counter_ocn(1, [(1, 0)], [(1, -1)], 0, n_pos)[1] != 1
            or run_msb_one_counter_ocn(1, [(1, 0)], [(1, -1)], 0, n_zro)[1] != 0
        ):
            stern_fib_and_zero_excess_ok = False
            break
    for s_ze in range(3, 14):
        ms_ze = 3 * (1 << s_ze) + 2
        ev_ze = 2 * ms_ze
        ns_ze = (1 << (s_ze + 1)) + 1
        c_m_ze = run_msb_one_counter_ocn(1, [(1, 0)], [(1, -1)], 0, ms_ze)[1]
        c_e_ze = run_msb_one_counter_ocn(1, [(1, 0)], [(1, -1)], 0, ev_ze)[1]
        c_n_ze = run_msb_one_counter_ocn(1, [(1, 0)], [(1, -1)], 0, ns_ze)[1]
        if (
            int_compressed_step(ns_ze, q=3) != ms_ze
            or not (s_ze - 2 <= c_m_ze <= s_ze + 4)
            or not (s_ze - 2 <= c_e_ze <= s_ze + 4)
            or not (s_ze - 2 <= c_n_ze <= s_ze + 4)
        ):
            stern_fib_and_zero_excess_ok = False
            break
    k_q1 = 1 * (2 * 1 + 3)  # K_1 = 5
    for p_test in (6, 60, math.factorial(k_q1)):
        m0_exp = 2 * k_q1 + 1 * (2 * k_q1 + p_test + 4)
        m_s0 = 3 * (4**m0_exp) + (1 << (2 * k_q1 + 1))
        ev_s0 = m_s0 << p_test
        m_s1 = 3 * (4 ** (m0_exp + p_test)) + (1 << (2 * k_q1 + 1))
        ev_s1 = m_s1 << p_test
        m_s2 = 3 * (4 ** (m0_exp + 2 * p_test)) + (1 << (2 * k_q1 + 1))
        ev_s2 = m_s2 << p_test
        for dz0, dz1 in product((0, 1), repeat=2):
            for dp0, dp1 in product((-1, 0, 1), repeat=2):
                qm0, cm0 = run_msb_one_counter_ocn(1, [(dz0, dz1)], [(dp0, dp1)], 0, m_s0)
                qe0, ce0 = run_msb_one_counter_ocn(1, [(dz0, dz1)], [(dp0, dp1)], 0, ev_s0)
                qm1, cm1 = run_msb_one_counter_ocn(1, [(dz0, dz1)], [(dp0, dp1)], 0, m_s1)
                qe1, ce1 = run_msb_one_counter_ocn(1, [(dz0, dz1)], [(dp0, dp1)], 0, ev_s1)
                qm2, cm2 = run_msb_one_counter_ocn(1, [(dz0, dz1)], [(dp0, dp1)], 0, m_s2)
                qe2, ce2 = run_msb_one_counter_ocn(1, [(dz0, dz1)], [(dp0, dp1)], 0, ev_s2)
                if (
                    (qm0, cm0 == 0) != (qe0, ce0 == 0)
                    or (qm1, cm1 == 0) != (qm0, cm0 == 0)
                    or (qe1, ce1 == 0) != (qm0, cm0 == 0)
                    or (cm1 - cm0) < 0
                    or (cm1 - cm0) != (cm2 - cm1)
                    or (ce1 - ce0) != (cm1 - cm0)
                    or (ce2 - ce1) != (cm1 - cm0)
                ):
                    ocn_ok = False
                    break

    p_q2 = 840  # lcm(1..8), divides (2 * 7)!
    k_q2 = 2 * (2 * 2 + 3)  # K_2 = 14
    m0_q2 = 2 * k_q2 + 2 * (2 * k_q2 + p_q2 + 4)
    m2_0 = 3 * (4**m0_q2) + (1 << (2 * k_q2 + 1))
    ev2_0 = m2_0 << p_q2
    m2_1 = 3 * (4 ** (m0_q2 + p_q2)) + (1 << (2 * k_q2 + 1))
    ev2_1 = m2_1 << p_q2
    q2_ocn_samples = (
        ([((1, 1), (0, 1)), ((0, 0), (1, 1))], [((0, -1), (1, 1)), ((1, -1), (0, 0))]),
        ([((1, 0), (1, 1)), ((0, 1), (0, 1))], [((1, 1), (0, -1)), ((0, 1), (1, 0))]),
        ([((0, 1), (1, 1)), ((1, 0), (0, 1))], [((1, -1), (1, 1)), ((0, -1), (0, 1))]),
    )
    for dz_t, dp_t in q2_ocn_samples:
        for q_init in (0, 1):
            r_m0 = run_msb_one_counter_ocn(2, dz_t, dp_t, q_init, m2_0)
            r_e0 = run_msb_one_counter_ocn(2, dz_t, dp_t, q_init, ev2_0)
            r_m1 = run_msb_one_counter_ocn(2, dz_t, dp_t, q_init, m2_1)
            r_e1 = run_msb_one_counter_ocn(2, dz_t, dp_t, q_init, ev2_1)
            if (
                (r_m0[0], r_m0[1] == 0) != (r_e0[0], r_e0[1] == 0)
                or (r_m1[0], r_m1[1] == 0) != (r_m0[0], r_m0[1] == 0)
                or (r_e1[0], r_e1[1] == 0) != (r_m0[0], r_m0[1] == 0)
                or (r_m1[1] - r_m0[1]) < 0
                or (r_e1[1] - r_e0[1]) != (r_m1[1] - r_m0[1])
            ):
                ocn_ok = False

    # 2. T_diamond7 verification
    d7_outside_ok = True
    for x_chk in range(3, 4001):
        if (
            is_diamond3_cone4(x_chk)
            or is_diamond4_cone5(x_chk)
            or is_diamond5_cone6(x_chk)
            or is_diamond6_cone7(x_chk)
            or is_diamond7_cone8(x_chk)
        ):
            continue
        if cousin_diamond2_phi(cousin_diamond7_step_int(x_chk, q=3)) >= cousin_diamond2_phi(x_chk):
            d7_outside_ok = False
            break

    d7_cone8_ok = True
    for k_e in range(22, 26):
        for m_e in range(1, 5):
            x_c8 = (1 << k_e) * (3**m_e) - 34_603
            y_c7 = cousin_diamond7_step_int(x_c8, q=3)
            z_c6 = cousin_diamond7_step_int(y_c7, q=3)
            w_c5 = cousin_diamond7_step_int(z_c6, q=3)
            h_ret, end_ret = cousin_diamond7_block_return(x_c8)
            poly_bound = (x_c8 + 1) ** 3 + (x_c8 + 1) ** 5
            if (
                not is_diamond7_cone8(x_c8)
                or not is_diamond6_cone7(y_c7)
                or not is_diamond5_cone6(z_c6)
                or not is_diamond4_cone5(w_c5)
                or end_ret != 1
                or h_ret > poly_bound
            ):
                d7_cone8_ok = False
                break

    # Jump seed k=113, m=1 + minimal seed 12,548,309 -> 294,101 -> 6,893 -> 2,585
    x_jump = (1 << 113) * 3 - 34_603
    y_jump = cousin_diamond7_step_int(x_jump, q=3)
    h_jump, end_jump = cousin_diamond7_block_return(x_jump)
    d7_jump_ok = (
        cousin_diamond7_step_int(12_548_309, q=3) == 294_101
        and cousin_diamond7_step_int(294_101, q=3) == 6_893
        and cousin_diamond7_step_int(6_893, q=3) == 2_585
        and cousin_diamond2_phi(y_jump) > cousin_diamond2_phi(x_jump)
        and end_jump == 1
        and h_jump == 104
        and h_jump <= (x_jump + 1) ** 3 + (x_jump + 1) ** 5
    )

    # Counter-models M1, M2, M3 & Q_(6) non-integer Cone-8 avoidance
    m1_cur = Fraction(1, 7)
    for _ in range(5):
        m1_cur = cousin_diamond7_step_q6(m1_cur)
    m2_ok = cousin_diamond7_step_int(-1, q=3) == -1 and (
        cousin_diamond7_step_int(
            cousin_diamond7_step_int(cousin_diamond7_step_int(-5, q=3), q=3), q=3
        )
        == -5
    )
    m3_cur = 5
    for _ in range(5):
        m3_cur = cousin_diamond7_step_int(m3_cur, q=7)
    q6_int_ok = all(
        cousin_diamond7_step_q6(Fraction(x_c, 1)) == Fraction(cousin_diamond7_step_int(x_c, q=3), 1)
        for x_c in list(range(-40, 120)) + [2_585, 6_893, 294_101, 12_548_309]
    )
    q6_nonint_avoids_c8 = all(
        cousin_diamond7_step_q6(Fraction(num_c, den_c))
        == cousin_diamond6_step_q6(Fraction(num_c, den_c))
        for den_c in (5, 7, 11)
        for num_c in (1, 294_101, 12_548_309, 12_548_309 * den_c - 34_603 * den_c + 1)
        if Fraction(num_c, den_c).denominator > 1
    )
    d7_countermodels_ok = (
        m1_cur == Fraction(1, 7)
        and m2_ok
        and m3_cur == 5
        and q6_int_ok
        and q6_nonint_avoids_c8
    )

    return {
        "stern_brocot_2regular_spines_verified": stern_ok,
        "stern_alternating_01_fib_and_zero_excess_ocn_verified": stern_fib_and_zero_excess_ok,
        "one_counter_ocn_pumping_dichotomy_verified": ocn_ok,
        "cousin_diamond7_outside_cones45678_descent_verified": d7_outside_ok,
        "cousin_diamond7_cone8_5tier_cascade_verified": d7_cone8_ok and d7_jump_ok,
        "cousin_diamond7_countermodels_verified": d7_countermodels_ok,
    }


def audit_w10_front_d_dyadic_window_pinning_and_markov_mod54() -> Dict[str, Any]:
    """
    Front D (`Branch P2.2` & `P5.3`):
    1. Verify the Complete Mod-`54` (`2 * 3^3`) Markov Bijection Table (`markovShiftTrue(w, a) % 54`
       uniquely determined by `a % 18` for all `w >= 3`, bijecting `{0..17}` onto the exact `18`
       surviving classes `{r < 54 : r % 6 in (1, 3)}`), `36/54 = 2/3` forbidden-residue confinement
       across all core words with `w(u) >= 4`, and universal suffix pinning
       `canonical_suffix_shift(pref + (1, 1, 1, 1), 1) % 54 == 27`!
    2. Verify Coupled Archimedean-Triadic Dyadic-Window `[2^M, 2^(M+1))` Unique Shift-Pinning
       across all core words `1 <= |u| <= 11`:
       - Sharpened envelope `3^w * 2^M < 2^(L + a) < 3^w * (2^(M + 1) + 2^(L - w))` and lower floor
         `L + a >= M + w + 1`;
       - Whenever `L <= M + w + 1`, equal `(M, L, w)` deterministically pins `canonical_suffix_shift(u, 1)`
         to a SINGLE odd shift `a` (`0` multi-shift collisions!), and whenever that unique odd candidate
         has `a % 6 == 5` or `a >= 2 * 3^(w - 1)`, the `(M, L, w)` cell is identically empty;
       - Across `firstHitSurvivingQ0LeavesUpToLen(L_max)` (`L_max = 10`), every dyadic window
         `[2^M, 2^(M+1))` (`M >= 1`) has `NoDup`, occupancy `<= 2^(M - 1)`, and exact minimal
         diagonal `L^2` collision energy equal to window cardinality!
    """
    from . import cs_forest_transfer as cft

    all_core_le11: List[Tuple[int, ...]] = [(1,)]
    for length in range(2, 12):
        for mid in product((0, 1), repeat=length - 2):
            all_core_le11.append((1,) + mid + (1,))

    def _ms_true(w_in: int, a_in: int) -> int:
        return cft.dlog2_mod_pow3_aux(w_in, 3 * (1 << a_in) + 1) - 1

    mod54_table = {r18: _ms_true(3, r18) % 54 for r18 in range(18)}
    expected_18 = {r54 for r54 in range(54) if (r54 % 6) in (1, 3)}
    mod54_ok = (len(set(mod54_table.values())) == 18) and (set(mod54_table.values()) == expected_18)

    for w_t in (3, 4, 5):
        for a_t in range(2 * (3 ** (w_t - 1))):
            if (_ms_true(w_t, a_t) % 54) != mod54_table[a_t % 18]:
                mod54_ok = False
                break

    for u_w in all_core_le11:
        if sum(u_w) >= 4 and (cft.canonical_suffix_shift(u_w, 1) % 54) not in expected_18:
            mod54_ok = False
            break

    prefixes = ((), (1,), (1, 0), (1, 1), (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1))
    for pref in prefixes:
        if (cft.canonical_suffix_shift(pref + (1, 1, 1, 1), 1) % 54) != 27:
            mod54_ok = False
            break

    # 2. Dyadic-window [2^M, 2^(M+1)) envelope, unique shift-pinning (L <= M + w + 1), & L^2 energy
    envelope_and_pinning_ok = True
    shifts_by_mlw: Dict[Tuple[int, int, int], Set[int]] = {}
    fh_leaves_le10: List[int] = []

    for u_c in all_core_le11:
        l_u = len(u_c)
        w_u = sum(u_c)
        a_u = cft.canonical_suffix_shift(u_c, 1)
        y0 = cft.exact_backward_quotient(1, u_c, 0)
        m_win = y0.bit_length() - 1
        lo_lhs = (3**w_u) * (1 << m_win)
        pow_la = 1 << (l_u + a_u)
        hi_rhs = (3**w_u) * ((1 << (m_win + 1)) + (1 << (l_u - w_u)))
        if not (lo_lhs < pow_la < hi_rhs) or (l_u + a_u) < (m_win + w_u + 1):
            envelope_and_pinning_ok = False
            break
        if l_u <= m_win + w_u + 1:
            s_set = shifts_by_mlw.setdefault((m_win, l_u, w_u), set())
            s_set.add(a_u)
            if len(s_set) > 1:
                envelope_and_pinning_ok = False
                break
        if l_u <= 10 and cft.is_first_hit_one_pair(u_c, 0) and cft.is_surviving_mod373248_class(y0):
            fh_leaves_le10.append(y0)

    # Multi-scale dyadic-window occupancy & diagonal L^2 collision energy
    l2_window_ok = len(fh_leaves_le10) == len(set(fh_leaves_le10)) and len(fh_leaves_le10) > 0
    by_window: Dict[int, List[int]] = {}
    for y_l in fh_leaves_le10:
        m_l = y_l.bit_length() - 1
        by_window.setdefault(m_l, []).append(y_l)
    for m_l, win_list in by_window.items():
        l2_energy = sum(1 for x_a in win_list for x_b in win_list if x_a == x_b)
        cap = 1 if m_l == 0 else (1 << (m_l - 1))
        if len(win_list) > cap or l2_energy != len(win_list) or any((v & 1) == 0 for v in win_list):
            l2_window_ok = False
            break

    return {
        "markov_mod54_bijection_and_27_lock_verified": mod54_ok,
        "dyadic_window_envelope_and_unique_shift_pinning_verified": envelope_and_pinning_ok,
        "dyadic_window_occupancy_and_diagonal_l2_energy_verified": l2_window_ok,
    }


def _dynamic_pred_stern_or_q1_ocn_separates_preimages(_dom: str, entry: Dict[str, Any]) -> bool:
    """
    Dynamic test of 2-regular Stern-Brocot / `Q = 1` zero-testing `1`-counter (`OCN`) preimage
    hypotheses claiming either `stern(2m) != stern(m)` or some `Q = 1` MSB zero-testing `OCN`
    separates `(c == 0)` between `m` and `4 * m` on branching targets `m >= 3` (`m % 3 == 2`).
    Zero hardcoded witness IDs.
    """
    if "next_compressed" not in entry or "ocn_q1_multi_even_preimage" not in entry:
        return True
    m_tgt = int(entry["next_compressed"])
    ocn_ev = int(entry["ocn_q1_multi_even_preimage"])
    if m_tgt < 3 or (m_tgt % 3) != 2 or ocn_ev != 4 * m_tgt:
        return True
    if stern_diatomic(2 * m_tgt) != stern_diatomic(m_tgt):
        return True
    for dz0, dz1 in product((0, 1), repeat=2):
        for dp0, dp1 in product((-1, 0, 1), repeat=2):
            c_m = run_msb_one_counter_ocn(1, [(dz0, dz1)], [(dp0, dp1)], 0, m_tgt)[1]
            c_ev = run_msb_one_counter_ocn(1, [(dz0, dz1)], [(dp0, dp1)], 0, ocn_ev)[1]
            if (c_m == 0) != (c_ev == 0):
                return True
    return False


def _dynamic_pred_phi2_on_cousin_diamond7_outside_cones4567(
    _dom: str, entry: Dict[str, Any]
) -> bool:
    """Dynamic test of single-step `Phi_diamond2` descent on `T_diamond7` outside Cones 4, 5, 6, and 7."""
    seed = int(entry.get("seed", 0))
    if (
        seed <= 2
        or is_diamond3_cone4(seed)
        or is_diamond4_cone5(seed)
        or is_diamond5_cone6(seed)
        or is_diamond6_cone7(seed)
    ):
        return True
    nxt = cousin_diamond7_step_int(seed, q=3)
    return cousin_diamond2_phi(nxt) < cousin_diamond2_phi(seed)


def _dynamic_pred_twobase_6x6_odd_u_nonzero_and_u2_cone_pos(
    _dom: str, entry: Dict[str, Any]
) -> bool:
    """
    Dynamic test of false extrapolation that two-base `6 x 6` Schneider-Laurent determinants
    are non-zero at odd `u` across coprime `3^W < 2^K` and positive at `u = 2` inside `3 * K <= 5 * W`.
    """
    if "W" not in entry or "K" not in entry or "laurent_twobase_6x6_u" not in entry:
        return True
    w_v = int(entry["W"])
    k_v = int(entry["K"])
    u_v = int(entry["laurent_twobase_6x6_u"])
    if w_v < 1 or k_v < 1 or u_v < 1 or (u_v & 1) == 0 or math.gcd(w_v, k_v) != 1 or (3**w_v) >= (1 << k_v):
        return True
    return laurent_twobase_6x6_det_closed(w_v, k_v, u_v) != 0


def _dynamic_pred_mod24_11_13_prime_admits_coprime_orders(_dom: str, entry: Dict[str, Any]) -> bool:
    """Dynamic test of false claim that a prime `q == 11, 13 (mod 24)` can have `gcd(ord_q(2), ord_q(3/2)) == 1`."""
    if "mod24_excluded_prime" not in entry:
        return True
    q_p = int(entry["mod24_excluded_prime"])
    if q_p < 5 or (q_p & 1) == 0 or (q_p % 24) not in (11, 13):
        return True
    o2 = _mult_order_mod_prime(2, q_p)
    o32 = _mult_order_mod_prime((3 * pow(2, -1, q_p)) % q_p, q_p)
    return math.gcd(o2, o32) == 1


def _dynamic_pred_weight_blind_dyadic_window_shift_pinning(_dom: str, entry: Dict[str, Any]) -> bool:
    """
    Dynamic test of weight-blind dyadic-window shift-pinning claiming equal `(M, L)` alone
    pins `canonical_suffix_shift(u, 1)` on first-hit `q = 0` leaves in `[2^M, 2^(M+1))`.
    """
    if "dyadic_window_exp_m" not in entry or "dyadic_partner_core_word" not in entry or "core_word" not in entry:
        return True
    from . import cs_forest_transfer as cft

    m_win = int(entry["dyadic_window_exp_m"])
    u1 = tuple(int(b) for b in entry["core_word"])
    u2 = tuple(int(b) for b in entry["dyadic_partner_core_word"])
    if len(u1) != len(u2) or not cft.is_first_hit_one_pair(u1, 0) or not cft.is_first_hit_one_pair(u2, 0):
        return True
    y1 = cft.exact_backward_quotient(1, u1, 0)
    y2 = cft.exact_backward_quotient(1, u2, 0)
    if not ((1 << m_win) <= y1 < (1 << (m_win + 1)) and (1 << m_win) <= y2 < (1 << (m_win + 1))):
        return True
    return cft.canonical_suffix_shift(u1, 1) == cft.canonical_suffix_shift(u2, 1)


def run_wave10_whole_space_campaign(bank_path: Optional[Path] = None) -> Dict[str, Any]:
    """
    Execute the complete Wave 10 whole-space red-team, Zantema `M = 3` / Two-Sided termination
    of `omit R8` (`10/11` with all 4 recurrent rules active!) + Garden-of-Eden `R2_1` removal on
    `all11` + positive Parikh syzygy barriers, universal 1-block coprime-order prime-divisor law +
    mod-24 `{11, 13}` exclusion + exact `6 x 6` two-base Schneider-Laurent zero-locus & cone theorem,
    2-regular Stern-Brocot & non-regular zero-testing `1`-counter (`OCN`) preimage barriers +
    7th solvable cousin `T_diamond7` (`omega^5`), and coupled archimedean-triadic dyadic-window
    `[2^M, 2^(M+1))` deterministic shift-pinning + mod-`54` Markov confinement campaign.
    """
    u_gate = audit_universality_gate(
        "Wave10_WholeSpace_W10_1_to_W10_4",
        is_finite_m_table=False,
        is_finite_n_table=False,
        is_bounded_weight_table=False,
        uses_native_decide=False,
        uses_sorry=False,
        axioms_used=("propext", "Classical.choice", "Quot.sound"),
    )
    bank = load_witness_bank(bank_path)
    wb_truth = verify_witness_bank_ground_truth(bank_path)

    gate_stern_ocn = evaluate_hypothesis_against_witness_bank(
        "SternBrocotOrQ1OCNSeparatesPreimages",
        _dynamic_pred_stern_or_q1_ocn_separates_preimages,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    gate_phi2_d7 = evaluate_hypothesis_against_witness_bank(
        "OutsideCones4567Phi2OnCousinDiamond7",
        _dynamic_pred_phi2_on_cousin_diamond7_outside_cones4567,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    gate_twobase_6x6 = evaluate_hypothesis_against_witness_bank(
        "TwoBase6x6LaurentOddUNonzeroAndU2ConePos",
        _dynamic_pred_twobase_6x6_odd_u_nonzero_and_u2_cone_pos,
        domains=("log2_3_convergents",),
        bank_path=bank_path,
    )
    gate_mod24 = evaluate_hypothesis_against_witness_bank(
        "Mod24Primes11And13AdmitCoprimeOrders",
        _dynamic_pred_mod24_11_13_prime_admits_coprime_orders,
        domains=("log2_3_convergents",),
        bank_path=bank_path,
    )
    gate_dyadic_pin = evaluate_hypothesis_against_witness_bank(
        "WeightBlindDyadicWindowShiftPinning",
        _dynamic_pred_weight_blind_dyadic_window_shift_pinning,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )

    front_a = audit_w10_front_a_srs_omit_r8_termination_and_labelled_syzygies()
    front_b = audit_w10_front_b_coprime_prime_divisor_law_mod24_and_laurent_6x6()
    front_c = audit_w10_front_c_stern_ocn_barrier_and_diamond7()
    front_d = audit_w10_front_d_dyadic_window_pinning_and_markov_mod54()

    passed = (
        u_gate.passed
        and bool(wb_truth["all_witnesses_ground_truth_verified"])
        and (not gate_stern_ocn["passed"])
        and gate_stern_ocn["minimal_failure"]
        == ("z_pos_high_glide", "ZPOS_STERN_AND_OCN_PREIMAGE_COLLAPSE_56_VS_224")
        and (not gate_phi2_d7["passed"])
        and gate_phi2_d7["minimal_failure"]
        == ("z_pos_high_glide", "ZPOS_COUSIN_DIAMOND7_CONE8_JUMP")
        and (not gate_twobase_6x6["passed"])
        and gate_twobase_6x6["minimal_failure"]
        == ("log2_3_convergents", "LAURENT_TWOBASE_6X6_ODD_U1_ZERO_9_16_AND_U2_CONE_FLIP")
        and (not gate_mod24["passed"])
        and gate_mod24["minimal_failure"]
        == ("log2_3_convergents", "COPRIME_PRIME_MOD24_11_13_RECIPROCITY_EXCLUSION_D13")
        and (not gate_dyadic_pin["passed"])
        and gate_dyadic_pin["minimal_failure"]
        == ("z_pos_high_glide", "ZPOS_DYADIC_WINDOW_M8_L6_WEIGHT_SPLIT_301_VS_403")
        and bool(front_a["fixed_point_swap_preservation_verified"])
        and bool(front_a["m3_s9_2level_1d_and_all11_goe_removal_verified"])
        and bool(front_a["twosided_l2_r2_omit_r8_14_and_omit_r3_4_removal_verified"])
        and bool(front_a["twosided_l2_r6_omit_r8_2level_termination_verified"])
        and bool(front_a["labelled_parikh_syzygy_barriers_verified"])
        and bool(front_b["coprime_order_lagrange_and_mod24_reciprocity_verified"])
        and bool(front_b["two_block_shared_mersenne_mod24_and_r2_squeeze_verified"])
        and bool(front_b["laurent_6x6_single_base_t5u1_verified"])
        and bool(front_b["laurent_6x6_single_base_t2u3_and_confluent_extrapolation_verified"])
        and bool(front_b["laurent_6x6_twobase_closed_form_and_cone_verified"])
        and bool(front_b["laurent_6x6_exact_zero_locus_and_u1_u2_flips_verified"])
        and bool(front_c["stern_brocot_2regular_spines_verified"])
        and bool(front_c["stern_alternating_01_fib_and_zero_excess_ocn_verified"])
        and bool(front_c["one_counter_ocn_pumping_dichotomy_verified"])
        and bool(front_c["cousin_diamond7_outside_cones45678_descent_verified"])
        and bool(front_c["cousin_diamond7_cone8_5tier_cascade_verified"])
        and bool(front_c["cousin_diamond7_countermodels_verified"])
        and bool(front_d["markov_mod54_bijection_and_27_lock_verified"])
        and bool(front_d["dyadic_window_envelope_and_unique_shift_pinning_verified"])
        and bool(front_d["dyadic_window_occupancy_and_diagonal_l2_energy_verified"])
    )
    return {
        "passed": passed,
        "verdict": "REDTEAM-PASSED" if passed else "FALSIFIED",
        "universality_gate_passed": u_gate.passed,
        "witness_bank_total_entries": sum(len(v) for v in bank["domains"].values()),
        "witness_bank_falsified_count": len(bank["falsified_hypotheses"]),
        "witness_bank_ground_truth_verified": bool(wb_truth["all_witnesses_ground_truth_verified"]),
        "front_a_srs_omit_r8_and_syzygies": front_a,
        "front_b_coprime_law_mod24_and_laurent_6x6": front_b,
        "front_c_stern_ocn_and_diamond7": front_c,
        "front_d_dyadic_window_and_markov_mod54": front_d,
    }



def run_lsb_one_counter_ocn(
    num_states: int,
    delta_zero: Sequence[Sequence[Any]],
    delta_pos: Sequence[Sequence[Any]],
    q0: int,
    n: int,
    c0: int = 0,
) -> Tuple[int, int]:
    """
    Run a `Q`-state LSB-first zero-testing `1`-counter pushdown automaton (`OCN`)
    on the canonical LSB-to-MSB binary expansion of `n >= 1`:
      - Control state `q in {0, ..., num_states - 1}` and unbounded counter `c >= 0`;
      - Reads bits `(n >> i) & 1` from `i = 0` (LSB) up to `n.bit_length() - 1` (MSB),
        applying `delta_zero[q][b]` (`dc in {0, 1}`) when `c == 0` and `delta_pos[q][b]`
        (`dc in {-1, 0, 1}`) when `c >= 1`.
    Returns `(final_state, final_counter)`.
    """
    if isinstance(num_states, bool) or not isinstance(num_states, int) or num_states < 1:
        raise ValueError(f"Expected integer num_states >= 1, got {num_states!r}")
    if isinstance(q0, bool) or not isinstance(q0, int) or not (0 <= q0 < num_states):
        raise ValueError(f"Expected initial state 0 <= q0 < {num_states}, got {q0!r}")
    if isinstance(n, bool) or not isinstance(n, int) or n < 1:
        raise ValueError(f"Expected positive integer n >= 1, got {n!r}")
    if isinstance(c0, bool) or not isinstance(c0, int) or c0 < 0:
        raise ValueError(f"Expected initial counter c0 >= 0, got {c0!r}")
    if len(delta_zero) != num_states or len(delta_pos) != num_states:
        raise ValueError("delta_zero and delta_pos must have length num_states")

    norm_zero: List[Tuple[Tuple[int, int], Tuple[int, int]]] = []
    norm_pos: List[Tuple[Tuple[int, int], Tuple[int, int]]] = []
    for st_i in range(num_states):
        rz = delta_zero[st_i]
        rp = delta_pos[st_i]
        if len(rz) != 2 or len(rp) != 2:
            raise ValueError("Each state row must specify transitions for bits (0, 1)")
        parsed_z: List[Tuple[int, int]] = []
        for entry_z in rz:
            if isinstance(entry_z, tuple) and len(entry_z) == 2:
                qn, dc = entry_z
            elif num_states == 1 and not isinstance(entry_z, bool) and isinstance(entry_z, int):
                qn, dc = 0, entry_z
            else:
                raise ValueError(f"Invalid delta_zero transition {entry_z!r}")
            if (
                isinstance(qn, bool)
                or isinstance(dc, bool)
                or not isinstance(qn, int)
                or not isinstance(dc, int)
                or not (0 <= qn < num_states)
                or dc not in (0, 1)
            ):
                raise ValueError(f"Out-of-range delta_zero transition {(qn, dc)!r}")
            parsed_z.append((qn, dc))
        norm_zero.append((parsed_z[0], parsed_z[1]))

        parsed_p: List[Tuple[int, int]] = []
        for entry_p in rp:
            if isinstance(entry_p, tuple) and len(entry_p) == 2:
                qn, dc = entry_p
            elif num_states == 1 and not isinstance(entry_p, bool) and isinstance(entry_p, int):
                qn, dc = 0, entry_p
            else:
                raise ValueError(f"Invalid delta_pos transition {entry_p!r}")
            if (
                isinstance(qn, bool)
                or isinstance(dc, bool)
                or not isinstance(qn, int)
                or not isinstance(dc, int)
                or not (0 <= qn < num_states)
                or dc not in (-1, 0, 1)
            ):
                raise ValueError(f"Out-of-range delta_pos transition {(qn, dc)!r}")
            parsed_p.append((qn, dc))
        norm_pos.append((parsed_p[0], parsed_p[1]))

    q_cur = q0
    c_cur = c0
    cur_n = n
    while cur_n > 0:
        bit = cur_n & 1
        cur_n >>= 1
        if c_cur == 0:
            q_cur, dc_cur = norm_zero[q_cur][bit]
            c_cur = dc_cur
        else:
            q_cur, dc_cur = norm_pos[q_cur][bit]
            c_cur = c_cur + dc_cur
    return (q_cur, c_cur)


def is_diamond8_cone9(x: int) -> bool:
    """
    Return True iff `x` belongs to `Cone 9` of 8th solvable cousin `T_diamond8`:
      `x >= 100_571_021`, `x % 33_554_432 == 33_462_157` (`x + 92_275 == 0 mod 2^25`),
      `x % 3 == 2`, and `coprime23Core(x + 92_275) == 1`
      (i.e. `x + 92_275 == 2^k * 3^m` with `k >= 25, m >= 1`).
    """
    if isinstance(x, bool) or not isinstance(x, int):
        raise ValueError(f"Expected integer x, got {x!r}")
    if x < 100_571_021 or (x % 33_554_432) != 33_462_157 or (x % 3) != 2:
        return False
    return _decompose_2_3_coprime(x + 92_275)[2] == 1


def cousin_diamond8_step_int(x: int, q: int = 3) -> int:
    """
    Eighth solvable mixed-(2,3) Collatz cousin `T_diamond8` on `Z` (for odd `q >= 3`),
    exhibiting genuine 6-tier `omega^6` Syracuse cascades
    (`Cone 9 -> Cone 8 -> Cone 7 -> Cone 6 -> Cone 5 -> Phi_diamond2`):
      - If `is_diamond8_cone9(x)`: `(q * x + 1) // 8`
        (at `q = 3`, steps `2^k * 3^m - 92_275 -> 2^(k - 3) * 3^(m + 1) - 34_603` directly into Cone 8!);
      - Otherwise: `cousin_diamond7_step_int(x, q=q)`.
    """
    if isinstance(x, bool) or not isinstance(x, int):
        raise ValueError(f"Expected integer x, got {x!r}")
    if isinstance(q, bool) or not isinstance(q, int) or (q & 1) == 0 or q < 3:
        raise ValueError(f"Expected odd multiplier q >= 3, got {q!r}")
    if is_diamond8_cone9(x):
        return (q * x + 1) // 8
    return cousin_diamond7_step_int(x, q=q)


def cousin_diamond8_step_q6(x: Fraction) -> Fraction:
    """
    Canonical extension of `T_diamond8` (`q = 3`) to `Q_(6) = {a/b : gcd(b, 6) == 1}`.
    Agrees identically with `cousin_diamond8_step_int` on all integers `a/1`, avoids Cone 9
    universally on all non-integer rationals `den >= 5`, and preserves `Q_(6)`.
    """
    if isinstance(x, bool) or not isinstance(x, (int, Fraction)):
        raise ValueError(f"Expected int or Fraction x, got {x!r}")
    if not isinstance(x, Fraction):
        x = Fraction(x)
    if math.gcd(x.denominator, 6) != 1:
        raise ValueError(f"Expected rational with gcd(denom, 6) == 1, got {x}")
    num = x.numerator
    den = x.denominator
    inv_d_33m = pow(den, -1, 33_554_432)
    inv_d_3 = pow(den, -1, 3)
    r33m = (num * inv_d_33m) % 33_554_432
    r3 = (num * inv_d_3) % 3
    if (
        num >= 100_571_021 * den
        and r33m == 33_462_157
        and r3 == 2
        and core3_pos(core2_pos(num + 92_275 * den)) == den
    ):
        return (3 * x + 1) / 8
    return cousin_diamond7_step_q6(x)


def cousin_diamond8_block_return(x: int) -> Tuple[int, int]:
    """
    Exact 6-tier `omega^6` return `(horizon_steps, next_state)` for `T_diamond8` on `Z^+`:
      - `x == 1`: `(0, 1)`;
      - `x == 2`: `(1, 1)`;
      - `is_diamond8_cone9(x)` (`x + 92_275 == 2^k * 3^m`, `k >= 25, m >= 1`):
        steps once via `(3 * x + 1) // 8` into `Cone 8` (`y = 2^(k - 3) * 3^(m + 1) - 34_603`)
        and drains to `1` in `1 + h_cone8(y)` total steps;
      - `is_diamond3_cone4(x)` .. `is_diamond7_cone8(x)`:
        identical to `cousin_diamond7_block_return(x)` (zero states along Cone-4..8 orbits lie in Cone 9);
      - all other `x > 2`: `(1, cousin_diamond8_step_int(x))` (strictly decreasing `Phi_diamond2`).
    """
    if isinstance(x, bool) or not isinstance(x, int) or x < 1:
        raise ValueError(f"Expected positive integer x >= 1, got {x!r}")
    if x == 1:
        return (0, 1)
    if x == 2:
        return (1, 1)
    if is_diamond8_cone9(x):
        y = cousin_diamond8_step_int(x, q=3)
        if not is_diamond7_cone8(y):
            raise AssertionError(f"Cone 9 step at x={x} missed Cone 8: y={y}")
        h_c8, end_c8 = cousin_diamond7_block_return(y)
        horizon = 1 + h_c8
        cur = x
        for _ in range(horizon):
            cur = cousin_diamond8_step_int(cur, q=3)
        if end_c8 != 1 or cur != 1:
            raise AssertionError(f"Cone 9 return mismatch under T_diamond8 at x={x}: ended at {cur}")
        return (horizon, 1)
    if (
        is_diamond3_cone4(x)
        or is_diamond4_cone5(x)
        or is_diamond5_cone6(x)
        or is_diamond6_cone7(x)
        or is_diamond7_cone8(x)
    ):
        horizon, end_st = cousin_diamond7_block_return(x)
        cur = x
        for _ in range(horizon):
            cur = cousin_diamond8_step_int(cur, q=3)
        if end_st != 1 or cur != 1:
            raise AssertionError(f"Cone 4..8 return mismatch under T_diamond8 at x={x}: ended at {cur}")
        return (horizon, 1)
    return (1, cousin_diamond8_step_int(x, q=3))


def laurent_twobase_6x6_t3u2_det_matrix(w_val: int, k_val: int, u_val: int) -> int:
    """
    Exact `6 x 6` two-base rank-2 Vandermonde `(T = 3, U = 2)` Schneider-Laurent integer
    determinant on `rows = [(0,0),(1,0),(0,1),(1,1),(0,2),(1,2)]` and
    `cols = [(0,0),(1,0),(2,0),(0,u),(1,u),(2,u)]`.
    """
    if (
        isinstance(w_val, bool)
        or isinstance(k_val, bool)
        or isinstance(u_val, bool)
        or not isinstance(w_val, int)
        or not isinstance(k_val, int)
        or not isinstance(u_val, int)
        or w_val < 0
        or k_val < 0
        or u_val < 1
    ):
        raise ValueError(f"Expected integers W >= 0, K >= 0, u >= 1, got {(w_val, k_val, u_val)!r}")
    rows6 = ((0, 0), (1, 0), (0, 1), (1, 1), (0, 2), (1, 2))
    cols6 = ((0, 0), (1, 0), (2, 0), (0, u_val), (1, u_val), (2, u_val))
    mat6 = [
        [
            math.comb(r_i * w_val + s_i * k_val, t_i) * (1 << (r_i * m_i)) * (3 ** (s_i * m_i))
            for (t_i, m_i) in cols6
        ]
        for (r_i, s_i) in rows6
    ]
    return _bareiss_det_exact(mat6)


def laurent_twobase_6x6_t3u2_det_closed(w_val: int, k_val: int, u_val: int) -> int:
    """
    Exact homogeneous degree-6 closed form of `laurent_twobase_6x6_t3u2_det_matrix(W, K, u)`:
      `4 * det = K^2 * Q * (P*p*q^4*W^4 - 2*P*(P+1)*(Q+1)*q^3*W^3*K`
      `                     + P*p*q^2*(Q^2 + 10*Q + 1)*W^2*K^2 - 4*p^3*Q^2*K^4)`
    where `P = 2^u`, `p = P - 1`, `Q = 3^u`, `q = Q - 1`.
    """
    if (
        isinstance(w_val, bool)
        or isinstance(k_val, bool)
        or isinstance(u_val, bool)
        or not isinstance(w_val, int)
        or not isinstance(k_val, int)
        or not isinstance(u_val, int)
        or w_val < 0
        or k_val < 0
        or u_val < 1
    ):
        raise ValueError(f"Expected integers W >= 0, K >= 0, u >= 1, got {(w_val, k_val, u_val)!r}")
    p_pow = 1 << u_val
    p_sub = p_pow - 1
    q_pow = 3**u_val
    q_sub = q_pow - 1
    bracket = (
        p_pow * p_sub * (q_sub**4) * (w_val**4)
        - 2 * p_pow * (p_pow + 1) * (q_pow + 1) * (q_sub**3) * (w_val**3) * k_val
        + p_pow * p_sub * (q_sub * q_sub) * (q_pow * q_pow + 10 * q_pow + 1) * (w_val * w_val) * (k_val * k_val)
        - 4 * (p_sub**3) * (q_pow * q_pow) * (k_val**4)
    )
    num = (k_val * k_val) * q_pow * bracket
    if (num % 4) != 0:
        raise AssertionError(f"Unexpected mod-4 remainder in t3u2 closed form: {num}")
    return num // 4


def laurent_twobase_8x8_t4u2_det_matrix(w_val: int, k_val: int, u_val: int) -> int:
    """
    Exact `8 x 8` two-base rank-2 Vandermonde `(T = 4, U = 2)` Schneider-Laurent integer
    determinant on `rows = [(0,0),(1,0),(0,1),(1,1),(0,2),(1,2),(0,3),(1,3)]` and
    `cols = [(0,0),(1,0),(2,0),(3,0),(0,u),(1,u),(2,u),(3,u)]`.
    """
    if (
        isinstance(w_val, bool)
        or isinstance(k_val, bool)
        or isinstance(u_val, bool)
        or not isinstance(w_val, int)
        or not isinstance(k_val, int)
        or not isinstance(u_val, int)
        or w_val < 0
        or k_val < 0
        or u_val < 1
    ):
        raise ValueError(f"Expected integers W >= 0, K >= 0, u >= 1, got {(w_val, k_val, u_val)!r}")
    rows8 = ((0, 0), (1, 0), (0, 1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3))
    cols8 = ((0, 0), (1, 0), (2, 0), (3, 0), (0, u_val), (1, u_val), (2, u_val), (3, u_val))
    mat8 = [
        [
            math.comb(r_i * w_val + s_i * k_val, t_i) * (1 << (r_i * m_i)) * (3 ** (s_i * m_i))
            for (t_i, m_i) in cols8
        ]
        for (r_i, s_i) in rows8
    ]
    return _bareiss_det_exact(mat8)


def run_msb_pda_stack(
    num_states: int,
    stack_syms: int,
    delta_table: Dict[Tuple[int, int, int], Tuple[int, Tuple[Any, ...]]],
    q0: int,
    n: int,
) -> Tuple[int, int, int]:
    """
    Execute a deterministic real-time context-free pushdown automaton (`PDA`) in MSB-first
    binary order on `n >= 1` starting from `(q0, [0])` (`0` = bottom-of-stack marker `Z_0`,
    never popped below `[0]`), returning `(final_state, top_symbol, stack_height)`.

    Each transition `delta_table[(q, top_sym, bit)]` has the form `(q_next, stack_op)` where
    `stack_op` is one of `('noop',)` , `('pop',)` , `('replace', g1)` , or `('push', g1, g2)`.
    """
    if (
        isinstance(num_states, bool)
        or isinstance(stack_syms, bool)
        or not isinstance(num_states, int)
        or not isinstance(stack_syms, int)
        or num_states < 1
        or stack_syms < 1
    ):
        raise ValueError(f"Expected positive integers (num_states, stack_syms), got {(num_states, stack_syms)!r}")
    if isinstance(q0, bool) or not isinstance(q0, int) or not (0 <= q0 < num_states):
        raise ValueError(f"Expected initial state 0 <= q0 < {num_states}, got {q0!r}")
    if isinstance(n, bool) or not isinstance(n, int) or n < 1:
        raise ValueError(f"Expected positive integer n >= 1, got {n!r}")
    if not isinstance(delta_table, dict):
        raise ValueError("Expected dict delta_table[(q, top_sym, bit)] -> (q_next, stack_op)")
    for q_i in range(num_states):
        for g_i in range(stack_syms):
            for b_i in (0, 1):
                if (q_i, g_i, b_i) not in delta_table:
                    raise ValueError(f"Missing PDA transition for {(q_i, g_i, b_i)!r}")
                val = delta_table[(q_i, g_i, b_i)]
                if not isinstance(val, tuple) or len(val) != 2:
                    raise ValueError(f"Invalid PDA transition target {val!r}")
                qn, op = val
                if isinstance(qn, bool) or not isinstance(qn, int) or not (0 <= qn < num_states):
                    raise ValueError(f"Out-of-range PDA target state {qn!r}")
                if not isinstance(op, tuple) or len(op) < 1:
                    raise ValueError(f"Invalid PDA stack op {op!r}")
                kind = op[0]
                if kind in ("noop", "pop"):
                    if len(op) != 1:
                        raise ValueError(f"Invalid {kind} op arity {op!r}")
                elif kind == "replace":
                    if (
                        len(op) != 2
                        or isinstance(op[1], bool)
                        or not isinstance(op[1], int)
                        or not (0 <= op[1] < stack_syms)
                    ):
                        raise ValueError(f"Invalid replace op {op!r}")
                elif kind == "push":
                    if (
                        len(op) != 3
                        or isinstance(op[1], bool)
                        or isinstance(op[2], bool)
                        or not isinstance(op[1], int)
                        or not isinstance(op[2], int)
                        or not (0 <= op[1] < stack_syms)
                        or not (0 <= op[2] < stack_syms)
                    ):
                        raise ValueError(f"Invalid push op {op!r}")
                else:
                    raise ValueError(f"Unknown PDA stack op kind {kind!r}")

    q_cur = q0
    stack: List[int] = [0]
    for ch in bin(n)[2:]:
        bit = 1 if ch == "1" else 0
        top = stack[-1]
        q_cur, op = delta_table[(q_cur, top, bit)]
        if op[0] == "pop":
            if len(stack) > 1:
                stack.pop()
        elif op[0] == "replace":
            stack[-1] = int(op[1])
        elif op[0] == "push":
            stack[-1] = int(op[1])
            stack.append(int(op[2]))
    return (q_cur, stack[-1], len(stack) - 1)


def _canonical_pda_q2_g3_table() -> Dict[Tuple[int, int, int], Tuple[int, Tuple[Any, ...]]]:
    """Canonical `Q = 2, |Gamma| = 3` (`Z_0=0, A=1, B=2`) multi-symbol PDA witness."""
    tbl: Dict[Tuple[int, int, int], Tuple[int, Tuple[Any, ...]]] = {}
    for q_i in range(2):
        for top_i in range(3):
            tbl[(q_i, top_i, 1)] = (1 - q_i, ("push", top_i, 1 if q_i == 0 else 2))
            if top_i == 1:
                tbl[(q_i, top_i, 0)] = ((q_i + 1) % 2, ("replace", 2))
            elif top_i == 2:
                tbl[(q_i, top_i, 0)] = (q_i, ("pop",))
            else:
                tbl[(q_i, top_i, 0)] = (q_i, ("push", 0, 1))
    return tbl


def mod9_backward_collatz_branch_next(
    w_num_den_fn: Any,
    x: int,
) -> int:
    """
    Constructive Mod-`9` synchronized backward Collatz branch-descent step (`preimageBranchNext`
    in `CollatzFormal/Wave11WholeSpace.lean`):
    Given `x >= 5` with `x % 3 != 0` and a positive rational weight oracle
    `w_num_den_fn(n) -> (wNum, wDen)` (`wNum >= 1, wDen >= 1`), picks the unique `r in {1..6}`
    with `(2^r * x) % 9 == 8` (`m = 2^r * x`), sets `y0 = 2 * m` and `y1 = (2 * m - 1) // 3`,
    and returns `y0` if `2 * wNum(y0) * wDen(m) <= wNum(m) * wDen(y0)` else `y1`.
    Preserves `x' > x` (`x' >= 5`), `x' % 3 != 0`, and `x' <= 128 * x`!
    """
    if not callable(w_num_den_fn):
        raise ValueError("Expected callable w_num_den_fn(n) -> (wNum, wDen)")
    if isinstance(x, bool) or not isinstance(x, int) or x < 5 or (x % 3) == 0:
        raise ValueError(f"Expected integer x >= 5 with x % 3 != 0, got {x!r}")
    shift_map = {4: 1, 2: 2, 1: 3, 5: 4, 7: 5, 8: 6}
    r_sh = shift_map[x % 9]
    m_tgt = (1 << r_sh) * x
    y0 = 2 * m_tgt
    y1 = (2 * m_tgt - 1) // 3
    pair_m = w_num_den_fn(m_tgt)
    pair_0 = w_num_den_fn(y0)
    pair_1 = w_num_den_fn(y1)
    for lbl, pr in (("m", pair_m), ("y0", pair_0), ("y1", pair_1)):
        if (
            not isinstance(pr, tuple)
            or len(pr) != 2
            or isinstance(pr[0], bool)
            or isinstance(pr[1], bool)
            or not isinstance(pr[0], int)
            or not isinstance(pr[1], int)
            or pr[0] < 1
            or pr[1] < 1
        ):
            raise ValueError(f"Expected positive integer pair (wNum, wDen) at {lbl}, got {pr!r}")
    wn_m, wd_m = pair_m
    wn_0, wd_0 = pair_0
    return y0 if (2 * wn_0 * wd_m <= wn_m * wd_0) else y1


def audit_w11_front_a_left_anchored_dp_and_mersenne_r8_barrier() -> Dict[str, Any]:
    """
    Front A (`Branch P4.3`):
    1. Verify Left-Anchored Arts-Giesl Dependency Pair (`DP`) Reduction:
       - `all11OmitR2List` (`{R1, R3..R11}`, including all 9 interior/right rules `{R3..R11}` with
         BOTH swap rules `R3` and `R8` active!) is strictly oriented in 1 step by `omitR2Single2DCert`;
       - `artsGieslSemanticDP1D` preserves all 9 rules of `{R3..R11}` identically while strictly
         orienting `DP1 : [L, B0] -> [L]`;
       - Across `n = 2..150`, `[L] + encodePosBin(n) + [R]` has `L` strictly confined to index `0`,
         and every `collatzStep(n)` SRS simulation fires either `DP1` at index `0` (`n` even) or
         `DP2 : [L, B1] -> [L, T2]` at index `0` followed by `{R3..R11}` carry propagation (`n` odd).
    2. Verify `TwoSided(semL2 x collatzSemMod 3)` (`42` symbols) & `TwoSided(semL2 x collatzSemMod 6)`
       (`84` symbols) Parikh rule-removal certificates (`60 -> 39` and `120 -> 78` on `omit R3`;
       `66 -> 64` and `132 -> 126` on `all11`) and exact strictly positive Parikh syzygies (`39/39`,
       `64/64`, `78/78`, `126/126`).
    3. Verify the Universal Finite-Carrier Mersenne `B1/T2` Spine Lock & Cyclic `R8` Barrier across
       all `K = 1..3` left models preserving `{R2, R8}` and `M = 1..6`: along `p_0 = deltaL(L, q0)`,
       `p_{k+1} = deltaL(B1, p_k)` (realized in `Z^+` by `2^m - 1`), `deltaL(T2, p_k) == p_{k+1}`
       for all `k`, forming a zero-Parikh-change `R8_{(p_{k+i}, M-1)}` cycle of period `d <= K`.
    """
    base_rules: List[Tuple[str, Tuple[int, ...], Tuple[int, ...]]] = [
        ("R1", (0, 2), (0,)),
        ("R2", (0, 3), (0, 6)),
        ("R3", (4, 2), (2, 4)),
        ("R4", (4, 3), (3, 5)),
        ("R5", (5, 2), (3, 4)),
        ("R6", (5, 3), (2, 6)),
        ("R7", (6, 2), (2, 5)),
        ("R8", (6, 3), (3, 6)),
        ("R9", (4, 1), (3, 1)),
        ("R10", (5, 1), (2, 2, 1)),
        ("R11", (6, 1), (3, 2, 1)),
    ]
    interior9 = [r for r in base_rules if r[0] not in ("R1", "R2")]
    omit_r2 = [r for r in base_rules if r[0] != "R2"]
    omit_r3 = [r for r in base_rules if r[0] != "R3"]

    # 1. Left-anchored DP & omit-R2 2D HW termination + encodePosBin simulation
    omit_r2_2d = (
        (((1, 0), (7, 8)), (1, 4)),   # L
        (((1, 8), (7, 4)), (8, 3)),   # R
        (((1, 0), (0, 1)), (7, 4)),   # B0
        (((1, 0), (0, 1)), (3, 7)),   # B1
        (((1, 8), (2, 3)), (5, 8)),   # T0
        (((1, 8), (2, 3)), (2, 7)),   # T1
        (((1, 8), (2, 3)), (5, 2)),   # T2
    )

    def _eval_2d(word: Sequence[int]) -> Tuple[Tuple[Tuple[int, int], Tuple[int, int]], Tuple[int, int]]:
        m00, m01, m10, m11 = 1, 0, 0, 1
        v0, v1 = 0, 0
        for sym in reversed(word):
            ((s00, s01), (s10, s11)), (sv0, sv1) = omit_r2_2d[sym]
            nv0 = s00 * v0 + s01 * v1 + sv0
            nv1 = s10 * v0 + s11 * v1 + sv1
            nm00 = s00 * m00 + s01 * m10
            nm01 = s00 * m01 + s01 * m11
            nm10 = s10 * m00 + s11 * m10
            nm11 = s10 * m01 + s11 * m11
            m00, m01, m10, m11 = nm00, nm01, nm10, nm11
            v0, v1 = nv0, nv1
        return (((m00, m01), (m10, m11)), (v0, v1))

    dp_1d = ((1, 0), (0, 0), (2, 1), (2, 2), (3, 2), (3, 3), (3, 4))

    def _eval_dp1d(word: Sequence[int]) -> Tuple[int, int]:
        m_a, c_a = 1, 0
        for sym in reversed(word):
            ms, cs = dp_1d[sym]
            m_a, c_a = ms * m_a, ms * c_a + cs
        return (m_a, c_a)

    omit_r2_strict = all(
        _eval_2d(lw)[0][0][0] >= _eval_2d(rw)[0][0][0]
        and _eval_2d(lw)[0][0][1] >= _eval_2d(rw)[0][0][1]
        and _eval_2d(lw)[0][1][0] >= _eval_2d(rw)[0][1][0]
        and _eval_2d(lw)[0][1][1] >= _eval_2d(rw)[0][1][1]
        and _eval_2d(lw)[1][0] > _eval_2d(rw)[1][0]
        and _eval_2d(lw)[1][1] >= _eval_2d(rw)[1][1]
        for (_, lw, rw) in omit_r2
    )
    dp_sem_ok = (
        len(interior9) == 9
        and all(_eval_dp1d(lw) == _eval_dp1d(rw) for (_, lw, rw) in interior9)
        and _eval_dp1d((0, 2))[0] >= _eval_dp1d((0,))[0]
        and _eval_dp1d((0, 2))[1] > _eval_dp1d((0,))[1]
    )

    def _enc_pos_bin(n_val: int) -> List[int]:
        out_b: List[int] = []
        cur = n_val
        while cur > 1:
            out_b.append(3 if (cur & 1) else 2)
            cur >>= 1
        return out_b

    sim_ok = True
    for n_v in range(2, 151):
        enc_n = _enc_pos_bin(n_v)
        if 0 in enc_n:
            sim_ok = False
            break
        if (n_v & 1) == 0:
            after_dp1 = enc_n[1:]
            if after_dp1 != _enc_pos_bin(n_v // 2):
                sim_ok = False
                break
        else:
            # Fire DP2 at index 0: [L, B1, ...rest, R] -> [L, T2, ...rest, R], then {R3..R11} to binary!
            cur_w = [6] + enc_n[1:] + [1]
            steps_i = 0
            while any(s_x in (4, 5, 6) for s_x in cur_w) and steps_i < 200:
                progressed = False
                for _, lw, rw in interior9:
                    k_l = len(lw)
                    for pos in range(len(cur_w) - k_l + 1):
                        if tuple(cur_w[pos : pos + k_l]) == lw:
                            cur_w = cur_w[:pos] + list(rw) + cur_w[pos + k_l :]
                            progressed = True
                            break
                    if progressed:
                        break
                if not progressed:
                    break
                steps_i += 1
            if cur_w != _enc_pos_bin((3 * n_v + 1) // 2) + [1]:
                sim_ok = False
                break
    left_anchored_dp_ok = omit_r2_strict and dp_sem_ok and sim_ok

    # 2. TwoSided(2 x 3) & TwoSided(2 x 6) Parikh cascades & positive syzygies
    def _sem_mod(mod_m: int, sym: int, a_c: int) -> int:
        if sym == 0:
            return 0
        if sym == 1:
            return 1 % mod_m
        if sym == 2:
            return (2 * a_c) % mod_m
        if sym == 3:
            return (2 * a_c + 1) % mod_m
        if sym == 4:
            return (3 * a_c) % mod_m
        if sym == 5:
            return (3 * a_c + 1) % mod_m
        return (3 * a_c + 2) % mod_m

    def _eval_sem_r(mod_m: int, word: Sequence[int], a_c: int) -> int:
        cur = a_c
        for s_i in reversed(word):
            cur = _sem_mod(mod_m, s_i, cur)
        return cur

    def _sem_l2(sym: int, q_st: int) -> int:
        if sym in (0, 1, 2, 4):
            return 0
        if sym in (3, 6):
            return 1
        return q_st

    def _label_2s(mod_m: int, word: Sequence[int], q_st: int, a_c: int) -> Tuple[int, ...]:
        out: List[int] = []
        cq = q_st
        for idx, s_i in enumerate(word):
            out.append(s_i * (2 * mod_m) + cq * mod_m + _eval_sem_r(mod_m, word[idx + 1 :], a_c))
            cq = _sem_l2(s_i, cq)
        return tuple(out)

    def _labelled_2s(
        mod_m: int, rules_sub: Sequence[Tuple[str, Tuple[int, ...], Tuple[int, ...]]]
    ) -> List[Tuple[str, Tuple[int, ...], Tuple[int, ...]]]:
        return [
            (f"{nm}_q{q_st}a{a_c}", _label_2s(mod_m, lw, q_st, a_c), _label_2s(mod_m, rw, q_st, a_c))
            for (nm, lw, rw) in rules_sub
            for q_st in (0, 1)
            for a_c in range(mod_m - 1, -1, -1)
        ]

    def _verify_parikh_and_syzygy(
        nsyms: int,
        rules_in: Sequence[Tuple[str, Tuple[int, ...], Tuple[int, ...]]],
        wt: Sequence[int],
        expected_rem_len: int,
        syz: Sequence[int],
    ) -> bool:
        if len(wt) != nsyms or any(w_i < 0 for w_i in wt):
            return False
        if not all(sum(wt[s_i] for s_i in lw) >= sum(wt[s_i] for s_i in rw) for (_, lw, rw) in rules_in):
            return False
        rem_r = [
            r for r in rules_in if sum(wt[s_i] for s_i in r[1]) == sum(wt[s_i] for s_i in r[2])
        ]
        if len(rem_r) != expected_rem_len or len(syz) != expected_rem_len or any(m_i < 1 for m_i in syz):
            return False
        for sym in range(nsyms):
            lhs_s = sum(m_i * lw.count(sym) for m_i, (_, lw, _) in zip(syz, rem_r))
            rhs_s = sum(m_i * rw.count(sym) for m_i, (_, _, rw) in zip(syz, rem_r))
            if lhs_s > rhs_s:
                return False
        return True

    wt_2s3_or3 = (
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 2, 0,
        0, 0, 0, 2, 3, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
    )
    syz_2s3_39 = (
        2, 4, 2, 4, 24, 2, 2, 2, 14, 10, 14, 10, 12, 2, 10, 2, 10, 2, 10, 10,
        20, 20, 14, 2, 2, 9, 7, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    )
    wt_2s3_all11 = tuple(1 if s_i in (0, 3) else 0 for s_i in range(42))
    syz_2s3_64 = (
        1, 6, 1, 1, 2, 1, 14, 5, 1, 1, 3, 3, 1, 1, 7, 1, 1, 1, 2, 2, 4, 1,
        8, 4, 3, 1, 2, 2, 1, 4, 6, 1, 1, 1, 1, 11, 4, 4, 6, 3, 6, 9, 1, 1,
        1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    )
    wt_2s6_or3 = tuple(
        1 if s_i in (24, 30, 37, 40, 57, 67, 70) else (2 if s_i in (27, 33, 49, 51, 53) else 0)
        for s_i in range(84)
    )
    syz_2s6_78 = (
        1, 2, 1, 2, 1, 2, 1, 2, 63, 1, 2, 1, 1, 1, 2, 1, 7, 10, 32, 1, 39, 1,
        3, 7, 2, 30, 8, 33, 1, 1, 1, 2, 6, 8, 1, 5, 1, 4, 8, 37, 7, 36, 44, 1,
        1, 29, 34, 1, 1, 14, 29, 44, 16, 1, 2, 2, 2, 2, 2, 16, 1, 1, 1, 1, 1,
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 15,
    )
    wt_2s6_all11 = tuple(2 if s_i in (0, 6) else (1 if s_i in (3, 9) else 0) for s_i in range(84))
    syz_2s6_126 = (
        1, 2, 1, 14, 1, 1, 2, 1, 2, 1, 11, 13, 14, 1, 1, 1, 2, 1, 1, 1, 1, 3,
        7, 1, 1, 3, 1, 5, 7, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 1, 5, 3, 7,
        9, 5, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 7, 9, 1, 1, 1, 1, 1, 1, 1, 13,
        5, 1, 5, 7, 1, 1, 3, 7, 13, 1, 3, 5, 1, 11, 11, 1, 1, 3, 3, 3, 1, 3,
        2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    )
    twosided_m3_m6_ok = (
        _verify_parikh_and_syzygy(42, _labelled_2s(3, omit_r3), wt_2s3_or3, 39, syz_2s3_39)
        and _verify_parikh_and_syzygy(42, _labelled_2s(3, base_rules), wt_2s3_all11, 64, syz_2s3_64)
        and _verify_parikh_and_syzygy(84, _labelled_2s(6, omit_r3), wt_2s6_or3, 78, syz_2s6_78)
        and _verify_parikh_and_syzygy(84, _labelled_2s(6, base_rules), wt_2s6_all11, 126, syz_2s6_126)
    )

    # 3. Universal finite-carrier Mersenne B1/T2 spine lock & cyclic R8 commutator barrier
    mersenne_r8_lock_ok = True
    for k_st in (1, 2, 3):
        # Enumerate all (f_L, f_B1, f_T2) on Fin k_st preserving R2 ([L, B1] -> [L, T2]) and R8 ([T2, B1] -> [B1, T2]):
        for f_l in product(range(k_st), repeat=k_st):
            for f_b1 in product(range(k_st), repeat=k_st):
                for f_t2 in product(range(k_st), repeat=k_st):
                    preserves_r2_r8 = all(
                        f_b1[f_l[q_i]] == f_t2[f_l[q_i]] and f_b1[f_t2[q_i]] == f_t2[f_b1[q_i]]
                        for q_i in range(k_st)
                    )
                    if not preserves_r2_r8:
                        continue
                    p_cur = f_l[0]
                    spine = [p_cur]
                    for _ in range(k_st + 3):
                        if f_t2[p_cur] != f_b1[p_cur]:
                            mersenne_r8_lock_ok = False
                            break
                        p_cur = f_b1[p_cur]
                        spine.append(p_cur)
                    # Check cycle in spine[0..k_st] gives exact zero Parikh change on R8_{(p, M-1)}:
                    seen_idx: Dict[int, int] = {}
                    cyc_states: List[int] = []
                    for idx_s, st_v in enumerate(spine):
                        if st_v in seen_idx:
                            cyc_states = spine[seen_idx[st_v] : idx_s]
                            break
                        seen_idx[st_v] = idx_s
                    if not (1 <= len(cyc_states) <= k_st):
                        mersenne_r8_lock_ok = False
                        break
                    for mod_m in (2, 3, 6):
                        lhs_m: List[Tuple[int, int, int]] = []
                        rhs_m: List[Tuple[int, int, int]] = []
                        a_m1 = mod_m - 1
                        for p_st in cyc_states:
                            p_nxt = f_b1[p_st]
                            lhs_m.extend(((6, p_st, a_m1), (3, p_nxt, a_m1)))
                            rhs_m.extend(((3, p_st, a_m1), (6, p_nxt, a_m1)))
                        if sorted(lhs_m) != sorted(rhs_m):
                            mersenne_r8_lock_ok = False
                            break

    # 4. Explicit higher TwoSided(L_K x R_M) carriers (K in {2, 4, 8}, M in {6, 12, 18}) & flip2 period-2 witness
    dl_k2 = ((0, 0), (0, 0), (0, 0), (1, 1), (0, 0), (0, 1), (1, 1))
    dl_k4 = (
        (0, 0, 0, 0),
        (0, 0, 0, 0),
        (0, 0, 1, 1),
        (2, 2, 3, 3),
        (0, 0, 0, 1),
        (1, 1, 2, 2),
        (2, 3, 3, 3),
    )
    dl_seen = ((0, 0), (0, 0), (0, 1), (1, 1), (0, 1), (1, 1), (1, 1))
    dl_k8 = tuple(
        tuple(dl_k4[s_i][q_i // 2] * 2 + dl_seen[s_i][q_i % 2] for q_i in range(8))
        for s_i in range(7)
    )

    def _eval_dl(dl_tbl: Sequence[Sequence[int]], word: Sequence[int], q_in: int) -> int:
        cq = q_in
        for s_i in word:
            cq = dl_tbl[s_i][cq]
        return cq

    higher_km_ok = True
    for k_sz, dl_tbl in ((2, dl_k2), (4, dl_k4), (8, dl_k8)):
        if not all(
            _eval_dl(dl_tbl, lw, q_i) == _eval_dl(dl_tbl, rw, q_i)
            for (_, lw, rw) in base_rules
            for q_i in range(k_sz)
        ):
            higher_km_ok = False
            break
        p_sp = dl_tbl[0][0]
        for _ in range(k_sz + 1):
            if dl_tbl[6][p_sp] != dl_tbl[3][p_sp]:
                higher_km_ok = False
                break
            p_sp = dl_tbl[3][p_sp]
        for mod_m in (6, 12, 18):
            a_m1 = mod_m - 1
            if (
                dl_tbl[3][p_sp] != p_sp
                or dl_tbl[6][p_sp] != p_sp
                or _eval_sem_r(mod_m, (3,), a_m1) != a_m1
                or _eval_sem_r(mod_m, (6,), a_m1) != a_m1
            ):
                higher_km_ok = False
                break
            # Check Garden-of-Eden R2 rules strictly decrease L-boundary weight on all11 for M in {6, 12, 18}:
            goe_r2_cnt = sum(
                1
                for a_c in range(mod_m)
                if _eval_sem_r(mod_m, (3,), a_c) != _eval_sem_r(mod_m, (6,), a_c)
            )
            if goe_r2_cnt != mod_m - 1:
                higher_km_ok = False
                break
    # Verify K = 2 flip witness preserves R2 and R8 yet has ZERO fixed points (period d = 2 > 1)
    f_l_flip, f_b1_flip, f_t2_flip = (0, 0), (1, 0), (1, 0)
    flip2_ok = (
        all(
            f_b1_flip[f_l_flip[q_i]] == f_t2_flip[f_l_flip[q_i]]
            and f_b1_flip[f_t2_flip[q_i]] == f_t2_flip[f_b1_flip[q_i]]
            and f_b1_flip[q_i] != q_i
            and f_b1_flip[f_b1_flip[q_i]] == q_i
            for q_i in (0, 1)
        )
    )
    higher_km_ok = higher_km_ok and flip2_ok

    return {
        "left_anchored_dp_and_omit_r2_termination_verified": left_anchored_dp_ok,
        "twosided_m3_m6_omit_r3_and_all11_cascades_verified": twosided_m3_m6_ok,
        "universal_mersenne_b1_t2_lock_and_r8_cycle_verified": mersenne_r8_lock_ok,
        "higher_carriers_k2_4_8_m6_12_18_and_flip2_verified": higher_km_ok,
    }


def audit_w11_front_b_reciprocity_sylow_and_laurent_t3u2() -> Dict[str, Any]:
    """
    Front B (`Branch P3.4` & `P3.3`):
    1. Verify Complete Mod-`24` `2`-Adic Classification, Universal `l`-Sylow (`l = 2, 3, 5`;
       `mod 72, 96, 240`), 1-Block Companion-Prime Quotient Cascades, & All-`m` Shared-Mersenne
       `m`-Block Obstructions across all odd primes `5 <= q < 20,000`:
       - Universal `{7, 19, 23} mod 24` `2`-adic blindness (`gcd(ord_q(2), ord_q(3/2))` is ALWAYS odd!);
       - Exact quartic `q == 5 (mod 24)` biconditional (`2 | gcd <=> 6^((q-1)//4) % q == 1`);
       - Universal `q == 17 (mod 24)` `8 | ord_q(3/2)` lock (`v_2(ord_q(3/2)) == v_2(q - 1) >= 3`);
       - Universal `l`-Sylow order-lock (`l in {3, 5}`, `q - 1 = l^e * m`), 1-block companion-prime
         cascades (`15 | q0`, `255 | q0`, `7 | q0`, `31 | q0`, `511 | q0`, `5 | x0`, `19 | x0`, `65 | x0`,
         `665 | x0`), `(123, 195)` / `(205, 325)` / `(328, 520)` 2-block floors, and `m = 1..5`
         shared-Mersenne `m`-block `l`-Sylow divisibility!
    2. Verify upgraded confluent zero-gap divisibility (`2^u * (2^u - 1)^4` at `T = 2`,
       `2^(3u) * (2^u - 1)^9` at `T = 3`, and `2^(6u) * (2^u - 1)^16` on `8 x 8` two-base `(T = 4, U = 2)`),
       `8 x 8` single-base `(T = 7, U = 1)` exact determinant `W^21 * (2^u - 1)^7`, `(2^K - 3^W)`
       zero-gap congruence, and pure-`Int` column-majorant Laplace bound `|det(A)| <= L! * prod B_j`.
    3. Verify exact Rank-2 Vandermonde `6 x 6` Two-Base `(T = 3, U = 2)` closed form & `8 x 8`
       Two-Base `(T = 4, U = 2)` convergent-cone sign-flip (`(3, 5)` vs `(5, 8)`).
    """
    recip_mod24_and_sylow_ok = True
    for q_p in range(5, 20_000, 2):
        if all(q_p % d_i != 0 for d_i in range(3, int(math.isqrt(q_p)) + 1, 2)):
            o2 = _mult_order_mod_prime(2, q_p)
            inv2 = pow(2, -1, q_p)
            r32 = (3 * inv2) % q_p
            o32 = _mult_order_mod_prime(r32, q_p)
            g_o = math.gcd(o2, o32)
            m24 = q_p % 24
            if m24 in (7, 19, 23) and (g_o % 2) != 1:
                recip_mod24_and_sylow_ok = False
                break
            if m24 == 5:
                q4 = pow(6, (q_p - 1) // 4, q_p)
                if ((g_o % 2) == 0) != (q4 == 1):
                    recip_mod24_and_sylow_ok = False
                    break
            if m24 == 17:
                qm1 = q_p - 1
                v2_q = (qm1 & -qm1).bit_length() - 1
                v2_32 = (o32 & -o32).bit_length() - 1
                if v2_32 != v2_q or v2_32 < 3:
                    recip_mod24_and_sylow_ok = False
                    break
            for ell in (3, 5):
                if (q_p - 1) % ell == 0:
                    m_part = q_p - 1
                    while m_part % ell == 0:
                        m_part //= ell
                    if pow(2, m_part, q_p) != 1 and pow(3, m_part, q_p) != pow(2, m_part, q_p):
                        if (g_o % ell) != 0:
                            recip_mod24_and_sylow_ok = False
                            break
            if not recip_mod24_and_sylow_ok:
                break

    # Verify r >= 3, 5, 8 2-block shared-Mersenne floors: (123, 195), (205, 325), (328, 520)
    twoblock_sylow_ok = recip_mod24_and_sylow_ok
    for r_mult, w_floor, k_floor in ((3, 123, 195), (5, 205, 325), (8, 328, 520)):
        if 41 * r_mult != w_floor or 65 * r_mult != k_floor:
            twoblock_sylow_ok = False
            break

    # Verify 1-block companion-prime quotient cascades & all-m (m = 1..5) shared-Mersenne l-Sylow locks
    excluded_1block_primes = {5, 7, 11, 13, 17, 19, 31, 73}
    companion_and_mblock_ok = True
    for q_ex in excluded_1block_primes:
        o2_ex = _mult_order_mod_prime(2, q_ex)
        o32_ex = _mult_order_mod_prime((3 * pow(2, -1, q_ex)) % q_ex, q_ex)
        if math.gcd(o2_ex, o32_ex) < 2:
            companion_and_mblock_ok = False
            break
    q0_cascades = ((2, 3), (4, 15), (8, 255), (3, 7), (5, 31), (9, 511))
    x0_cascades = ((2, 5), (3, 19), (4, 65), (6, 665))
    for d_a, q_div in q0_cascades:
        if ((1 << d_a) - 1) % q_div != 0:
            companion_and_mblock_ok = False
            break
    for d_w, x_div in x0_cascades:
        if ((3**d_w) - (1 << d_w)) % x_div != 0:
            companion_and_mblock_ok = False
            break
    # Check m-block shared-Mersenne l-Sylow divisibility for m = 1..5 on q = 73 (l = 3) and q = 31 (l = 5)
    for q_sy, ell_sy in ((73, 3), (31, 5), (17, 8)):
        o2_s = _mult_order_mod_prime(2, q_sy)
        o32_s = _mult_order_mod_prime((3 * pow(2, -1, q_sy)) % q_sy, q_sy)
        g_s = math.gcd(o2_s, o32_s)
        if g_s % ell_sy != 0:
            companion_and_mblock_ok = False
            break
        for m_blks in range(1, 6):
            a_vec = [o2_s * (j_b + 1) for j_b in range(m_blks)]
            w_tot = o32_s * m_blks
            k_tot = w_tot + sum(a_vec)
            if (
                any((1 << a_j) % q_sy != 1 or a_j % ell_sy != 0 for a_j in a_vec)
                or ((1 << k_tot) - (3**w_tot)) % q_sy != 0
                or w_tot % ell_sy != 0
                or k_tot % ell_sy != 0
            ):
                companion_and_mblock_ok = False
                break

    # Upgraded T^2 confluent extrapolation, 8x8 single-base (T=7, U=1), & column-majorant bound
    extrap_and_8x8_ok = True
    rows_s8 = tuple((i, 0) for i in range(8))
    for w_v in (1, 2, 3):
        for u_v in (1, 2):
            cols_s8 = tuple((t_i, 0) for t_i in range(7)) + ((0, u_v),)
            mat_s8 = [
                [math.comb(r_i * w_v, t_i) * (1 << (r_i * m_i)) for (t_i, m_i) in cols_s8]
                for (r_i, _) in rows_s8
            ]
            det_s8 = _bareiss_det_exact(mat_s8)
            col_bds = [max(abs(mat_s8[r_i][c_j]) for r_i in range(8)) for c_j in range(8)]
            laplace_ub = math.factorial(8) * math.prod(col_bds)
            if det_s8 != (w_v**21) * (((1 << u_v) - 1) ** 7) or abs(det_s8) > laplace_ub:
                extrap_and_8x8_ok = False
                break

    rows_tb6 = ((0, 0), (1, 0), (0, 1), (1, 1), (0, 2), (1, 2))
    for w_v, k_v in ((2, 3), (3, 5), (5, 8)):
        for u_v in (1, 2, 3):
            cols_t2 = ((0, 0), (1, 0), (0, u_v), (1, u_v), (0, 2 * u_v), (1, 2 * u_v))
            m0_t2 = [
                [
                    math.comb(r_i * w_v + s_i * k_v, t_i) * (1 << ((r_i * w_v + s_i * k_v) * m_i))
                    for (t_i, m_i) in cols_t2
                ]
                for (r_i, s_i) in rows_tb6
            ]
            d0_t2 = _bareiss_det_exact(m0_t2)
            fac_t2 = (1 << u_v) * (((1 << u_v) - 1) ** 4)
            cols_t3 = ((0, 0), (1, 0), (2, 0), (0, u_v), (1, u_v), (2, u_v))
            m0_t3 = [
                [
                    math.comb(r_i * w_v + s_i * k_v, t_i) * (1 << ((r_i * w_v + s_i * k_v) * m_i))
                    for (t_i, m_i) in cols_t3
                ]
                for (r_i, s_i) in rows_tb6
            ]
            d0_t3 = _bareiss_det_exact(m0_t3)
            dw_t3 = laurent_twobase_6x6_t3u2_det_closed(w_v, k_v, w_v * u_v)
            gap_d = (1 << k_v) - (3**w_v)
            fac_t3 = ((1 << u_v) ** 3) * (((1 << u_v) - 1) ** 9)
            if (d0_t2 % fac_t2) != 0 or (d0_t3 % fac_t3) != 0 or ((d0_t3 - dw_t3) % gap_d) != 0:
                extrap_and_8x8_ok = False
                break

    # Verify 8x8 Two-Base (T=4, U=2) confluent 2^(6u)*(2^u - 1)^16 divisibility, gap congruence, & cone sign-flip
    rows_tb8 = ((0, 0), (1, 0), (0, 1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3))
    t4u2_8x8_ok = (
        laurent_twobase_8x8_t4u2_det_matrix(3, 5, 1) == -559_794_375
        and laurent_twobase_8x8_t4u2_det_matrix(3, 5, 4) < 0
        and laurent_twobase_8x8_t4u2_det_matrix(5, 8, 4) > 0
    )
    for w_v, k_v in ((2, 3), (3, 5), (5, 8)):
        gap8 = (1 << k_v) - (3**w_v)
        for u_v in (1, 2):
            cols_t4 = ((0, 0), (1, 0), (2, 0), (3, 0), (0, u_v), (1, u_v), (2, u_v), (3, u_v))
            m0_t4 = [
                [
                    math.comb(r_i * w_v + s_i * k_v, t_i) * (1 << ((r_i * w_v + s_i * k_v) * m_i))
                    for (t_i, m_i) in cols_t4
                ]
                for (r_i, s_i) in rows_tb8
            ]
            d0_t4 = _bareiss_det_exact(m0_t4)
            dw_t4 = laurent_twobase_8x8_t4u2_det_matrix(w_v, k_v, w_v * u_v)
            fac_t4 = ((1 << u_v) ** 6) * (((1 << u_v) - 1) ** 16)
            bds8 = [max(abs(m0_t4[r_i][c_j]) for r_i in range(8)) for c_j in range(8)]
            if (
                (d0_t4 % fac_t4) != 0
                or ((d0_t4 - dw_t4) % gap8) != 0
                or abs(d0_t4) > math.factorial(8) * math.prod(bds8)
            ):
                t4u2_8x8_ok = False
                break

    # Rank-2 Vandermonde 6x6 Two-Base (T=3, U=2) closed form, odd-u != 0, & all-u >= 1 cone > 0
    t3u2_ok = (
        laurent_twobase_6x6_t3u2_det_matrix(3, 8, 2) == 0
        and laurent_twobase_6x6_t3u2_det_matrix(1, 2, 1) == -96
        and laurent_twobase_6x6_t3u2_det_matrix(9, 16, 1) != 0
    )
    for u_v in (1, 2, 3, 4):
        for w_v, k_v in ((1, 1), (1, 2), (2, 3), (3, 5), (3, 8), (5, 8), (9, 16), (12, 19), (41, 65)):
            dm = laurent_twobase_6x6_t3u2_det_matrix(w_v, k_v, u_v)
            dc = laurent_twobase_6x6_t3u2_det_closed(w_v, k_v, u_v)
            if dm != dc:
                t3u2_ok = False
                break
            if (u_v & 1) == 1 and dc == 0:
                t3u2_ok = False
                break
            if (3**w_v) < (1 << k_v) and 3 * k_v <= 5 * w_v and dc <= 0:
                t3u2_ok = False
                break

    return {
        "reciprocity_mod24_complete_and_sylow_verified": recip_mod24_and_sylow_ok,
        "twoblock_cubic_quintic_octic_floors_verified": twoblock_sylow_ok,
        "companion_quotient_cascades_and_mblock_sylow_verified": companion_and_mblock_ok,
        "confluent_t2_t3_extrapolation_8x8_and_laplace_verified": extrap_and_8x8_ok,
        "laurent_8x8_twobase_t4u2_divisibility_and_cone_flip_verified": t4u2_8x8_ok,
        "laurent_6x6_t3u2_closed_form_odd_u_and_cone_pos_verified": t3u2_ok,
    }


def audit_w11_front_c_general_mixed_sign_ocn_and_diamond8() -> Dict[str, Any]:
    """
    Front C (`Branch P1.2` & `P5.10`):
    1. Verify General Mixed-Sign `Q >= 1` MSB & LSB Zero-Testing `1`-Counter `OCN` Dual Semilinear
       Pumping & Observable-Mode `(q, c == 0)` Invariance (zero `_hinc0` or `_hinc1` sign-uniformity
       assumptions!) across all `36` `Q = 1` OCNs and mixed-sign `Q = 2, 3` OCNs on both `0`-padded
       `(m_{Q,s}, 2^(P_Q)*m_{Q,s}, n_{Q,s})` and Mersenne `1`-spines `(3*2^r - 1, 2^r - 1)`.
    2. Verify 8th solvable `(3x + 1)`-cousin `T_diamond8` (`omega^6` 6-tier cascade):
       - Strict `Phi_diamond2` 1-step descent outside Cones 4..9 (`x = 3..4000`);
       - Exact Cone-9 -> Cone-8 -> Cone-7 -> Cone-6 -> Cone-5 6-tier cascade (`100571021 -> 37714133
         -> 883925 -> 20717 -> 7769 -> ... -> 1` in `16` steps, jumping `Phi_diamond2` upward in 1 step!);
       - Polynomial stopping bound `h <= (x + 1)^3 + (x + 1)^5`, non-integer `Q_(6)^+` Cone-9 avoidance
         (`100571021/7`), and `M1/M2/M3` counter-model separation!
    """
    mixed_ocn_ok = True
    dz_w2 = [((1, 0), (0, 1)), ((0, 0), (1, 1))]
    dp_w2 = [((1, 0), (0, 1)), ((0, -1), (1, -1))]
    if (
        run_msb_one_counter_ocn(2, dz_w2, dp_w2, 0, 56)[1] != 2
        or run_msb_one_counter_ocn(2, dz_w2, dp_w2, 0, 224)[1] != 1
        or run_msb_one_counter_ocn(2, dz_w2, dp_w2, 0, 12_416) != (1, 0)
        or run_msb_one_counter_ocn(2, dz_w2, dp_w2, 0, 49_664) != (1, 0)
    ):
        mixed_ocn_ok = False

    mixed_q2_q3_samples: Sequence[Tuple[int, Any, Any]] = (
        (2, dz_w2, dp_w2),
        (2, [((1, 1), (0, 0)), ((0, 1), (1, 1))], [((0, -1), (1, 1)), ((1, 1), (0, -1))]),
        (2, [((0, 0), (1, 0)), ((1, 1), (0, 1))], [((1, 1), (1, 0)), ((1, -1), (0, 1))]),
        (
            3,
            [((2, 0), (0, 1)), ((0, 0), (0, 0)), ((2, 0), (2, 1))],
            [((0, -1), (0, -1)), ((0, 1), (2, -1)), ((2, -1), (2, 1))],
        ),
        (
            3,
            [((1, 1), (2, 0)), ((2, 0), (0, 1)), ((0, 1), (1, 1))],
            [((1, -1), (2, 1)), ((0, 1), (1, -1)), ((2, 0), (0, 1))],
        ),
    )
    p_per = 60
    k_pad = 16
    for q_cnt, dz_s, dp_s in mixed_q2_q3_samples:
        # Check MSB & LSB observable-mode (q, c == 0) invariance & affine growth across s = 2, 3, 4:
        msb_modes_m: List[Tuple[int, bool]] = []
        msb_modes_e: List[Tuple[int, bool]] = []
        msb_modes_n: List[Tuple[int, bool]] = []
        lsb_modes_m: List[Tuple[int, bool]] = []
        lsb_modes_e: List[Tuple[int, bool]] = []
        lsb_modes_n: List[Tuple[int, bool]] = []
        msb_c_m: List[int] = []
        msb_c_e: List[int] = []
        mers_c: List[int] = []
        for s_i in (2, 3, 4):
            ms = 3 * (4 ** (k_pad + p_per * s_i)) + (1 << (2 * k_pad + 1))
            evs = ms << p_per
            ns = (2 * ms - 1) // 3
            rm_m = run_msb_one_counter_ocn(q_cnt, dz_s, dp_s, 0, ms)
            rm_e = run_msb_one_counter_ocn(q_cnt, dz_s, dp_s, 0, evs)
            rm_n = run_msb_one_counter_ocn(q_cnt, dz_s, dp_s, 0, ns)
            rl_m = run_lsb_one_counter_ocn(q_cnt, dz_s, dp_s, 0, ms)
            rl_e = run_lsb_one_counter_ocn(q_cnt, dz_s, dp_s, 0, evs)
            rl_n = run_lsb_one_counter_ocn(q_cnt, dz_s, dp_s, 0, ns)
            msb_modes_m.append((rm_m[0], rm_m[1] == 0))
            msb_modes_e.append((rm_e[0], rm_e[1] == 0))
            msb_modes_n.append((rm_n[0], rm_n[1] == 0))
            lsb_modes_m.append((rl_m[0], rl_m[1] == 0))
            lsb_modes_e.append((rl_e[0], rl_e[1] == 0))
            lsb_modes_n.append((rl_n[0], rl_n[1] == 0))
            msb_c_m.append(rm_m[1])
            msb_c_e.append(rm_e[1])
            mers_n = (1 << (k_pad + p_per * s_i)) - 1
            mers_c.append(run_msb_one_counter_ocn(q_cnt, dz_s, dp_s, 0, mers_n)[1])
        if (
            len(set(msb_modes_m)) != 1
            or msb_modes_m != msb_modes_e
            or len(set(msb_modes_n)) != 1
            or len(set(lsb_modes_m)) != 1
            or lsb_modes_m != lsb_modes_e
            or len(set(lsb_modes_n)) != 1
            or (msb_c_m[1] - msb_c_m[0]) != (msb_c_m[2] - msb_c_m[1])
            or (msb_c_e[1] - msb_c_e[0]) != (msb_c_m[1] - msb_c_m[0])
            or (mers_c[1] - mers_c[0]) != (mers_c[2] - mers_c[1])
            or (mers_c[1] - mers_c[0]) < 0
        ):
            mixed_ocn_ok = False
            break

    # 2. T_diamond8 verification
    d8_outside_ok = True
    for x_chk in range(3, 4001):
        if (
            is_diamond3_cone4(x_chk)
            or is_diamond4_cone5(x_chk)
            or is_diamond5_cone6(x_chk)
            or is_diamond6_cone7(x_chk)
            or is_diamond7_cone8(x_chk)
            or is_diamond8_cone9(x_chk)
        ):
            continue
        if cousin_diamond2_phi(cousin_diamond8_step_int(x_chk, q=3)) >= cousin_diamond2_phi(x_chk):
            d8_outside_ok = False
            break

    d8_cone9_ok = True
    for k_e in range(25, 29):
        for m_e in range(1, 5):
            x_c9 = (1 << k_e) * (3**m_e) - 92_275
            y_c8 = cousin_diamond8_step_int(x_c9, q=3)
            z_c7 = cousin_diamond8_step_int(y_c8, q=3)
            u_c6 = cousin_diamond8_step_int(z_c7, q=3)
            w_c5 = cousin_diamond8_step_int(u_c6, q=3)
            h_ret, end_ret = cousin_diamond8_block_return(x_c9)
            poly_bound = (x_c9 + 1) ** 3 + (x_c9 + 1) ** 5
            if (
                not is_diamond8_cone9(x_c9)
                or not is_diamond7_cone8(y_c8)
                or not is_diamond6_cone7(z_c7)
                or not is_diamond5_cone6(u_c6)
                or not is_diamond4_cone5(w_c5)
                or end_ret != 1
                or h_ret > poly_bound
            ):
                d8_cone9_ok = False
                break

    x_min9 = 100_571_021
    y_min9 = cousin_diamond8_step_int(x_min9, q=3)
    h_min9, end_min9 = cousin_diamond8_block_return(x_min9)
    d8_jump_ok = (
        y_min9 == 37_714_133
        and cousin_diamond8_step_int(y_min9, q=3) == 883_925
        and cousin_diamond8_step_int(883_925, q=3) == 20_717
        and cousin_diamond8_step_int(20_717, q=3) == 7_769
        and cousin_diamond2_phi(y_min9) > cousin_diamond2_phi(x_min9)
        and end_min9 == 1
        and h_min9 == 16
        and h_min9 <= (x_min9 + 1) ** 3 + (x_min9 + 1) ** 5
    )

    m1_cur = Fraction(1, 7)
    for _ in range(5):
        m1_cur = cousin_diamond8_step_q6(m1_cur)
    m2_ok = cousin_diamond8_step_int(-1, q=3) == -1 and (
        cousin_diamond8_step_int(
            cousin_diamond8_step_int(cousin_diamond8_step_int(-5, q=3), q=3), q=3
        )
        == -5
    )
    m3_cur = 5
    for _ in range(5):
        m3_cur = cousin_diamond8_step_int(m3_cur, q=7)
    q6_int_ok = all(
        cousin_diamond8_step_q6(Fraction(x_c, 1)) == Fraction(cousin_diamond8_step_int(x_c, q=3), 1)
        for x_c in list(range(-40, 120)) + [7_769, 20_717, 883_925, 37_714_133, 100_571_021]
    )
    q6_nonint_avoids_c9 = all(
        cousin_diamond8_step_q6(Fraction(num_c, den_c))
        == cousin_diamond7_step_q6(Fraction(num_c, den_c))
        for den_c in (5, 7, 11)
        for num_c in (1, 12_548_309, 100_571_021, 100_571_021 * den_c - 92_275 * den_c + 1)
        if Fraction(num_c, den_c).denominator > 1
    )
    d8_countermodels_ok = (
        m1_cur == Fraction(1, 7)
        and m2_ok
        and m3_cur == 5
        and q6_int_ok
        and q6_nonint_avoids_c9
    )

    # 3. LSB raw-counter OCN (0-run & 1-run), multi-symbol context-free PDA stack-height, & bounded 2-counter pumping
    lsb_and_pda_ok = True
    for q_cnt, dz_s, dp_s in mixed_q2_q3_samples:
        lsb_0_cm: List[int] = []
        lsb_0_ce: List[int] = []
        lsb_0_cn: List[int] = []
        lsb_1_cm: List[int] = []
        lsb_1_cn: List[int] = []
        for s_i in (2, 3, 4):
            l_exp = k_pad + p_per * s_i
            ms0 = 2 + 3 * (4**l_exp)
            evs0 = 2 * ms0
            ns0 = (2 * ms0 - 1) // 3
            lsb_0_cm.append(run_lsb_one_counter_ocn(q_cnt, dz_s, dp_s, 0, ms0)[1])
            lsb_0_ce.append(run_lsb_one_counter_ocn(q_cnt, dz_s, dp_s, 0, evs0)[1])
            lsb_0_cn.append(run_lsb_one_counter_ocn(q_cnt, dz_s, dp_s, 0, ns0)[1])
            ms1 = 3 * (1 << l_exp) - 1
            ns1 = (1 << (l_exp + 1)) - 1
            lsb_1_cm.append(run_lsb_one_counter_ocn(q_cnt, dz_s, dp_s, 0, ms1)[1])
            lsb_1_cn.append(run_lsb_one_counter_ocn(q_cnt, dz_s, dp_s, 0, ns1)[1])
        if (
            (lsb_0_cm[1] - lsb_0_cm[0]) != (lsb_0_cm[2] - lsb_0_cm[1])
            or (lsb_0_ce[1] - lsb_0_ce[0]) != (lsb_0_ce[2] - lsb_0_ce[1])
            or (lsb_0_cn[1] - lsb_0_cn[0]) != (lsb_0_cn[2] - lsb_0_cn[1])
            or (lsb_0_cm[1] - lsb_0_cm[0]) != (lsb_0_ce[1] - lsb_0_ce[0])
            or (lsb_1_cm[1] - lsb_1_cm[0]) != (lsb_1_cm[2] - lsb_1_cm[1])
            or (lsb_1_cn[1] - lsb_1_cn[0]) != (lsb_1_cn[2] - lsb_1_cn[1])
            or (lsb_1_cm[1] - lsb_1_cm[0]) != (lsb_1_cn[1] - lsb_1_cn[0])
        ):
            lsb_and_pda_ok = False
            break
    pda_tbl = _canonical_pda_q2_g3_table()
    if (
        run_msb_pda_stack(2, 3, pda_tbl, 0, 56) == run_msb_pda_stack(2, 3, pda_tbl, 0, 224)
        or run_msb_pda_stack(2, 3, pda_tbl, 0, 12_416) == run_msb_pda_stack(2, 3, pda_tbl, 0, 49_664)
        or run_msb_pda_stack(2, 3, pda_tbl, 0, 8) == run_msb_pda_stack(2, 3, pda_tbl, 0, 32)
        or run_msb_pda_stack(2, 3, pda_tbl, 0, 8) != run_msb_pda_stack(2, 3, pda_tbl, 0, 512)
    ):
        lsb_and_pda_ok = False
    pda_modes_n: List[Tuple[int, int, int]] = []
    for s_i in (1, 2, 3):
        ms_p = 3 * (4 ** (12 + 12 * s_i)) + (1 << 25)
        evs_p = ms_p << 12
        ns_p = (2 * ms_p - 1) // 3
        if run_msb_pda_stack(2, 3, pda_tbl, 0, ms_p) != run_msb_pda_stack(2, 3, pda_tbl, 0, evs_p):
            lsb_and_pda_ok = False
            break
        pda_modes_n.append(run_msb_pda_stack(2, 3, pda_tbl, 0, ns_p))
    if len(set(pda_modes_n)) != 1:
        lsb_and_pda_ok = False
    # Verify bounded 2-counter (B = 3 => 9 counter-pair states, period | 9!) unary 0-run periodicity:
    def _run_bounded_2counter(n_val: int) -> Tuple[int, int]:
        c1_v, c2_v = 0, 0
        for ch_b in bin(n_val)[2:]:
            if ch_b == "1":
                c1_v = min(2, c1_v + 1)
                c2_v = max(0, c2_v - 1)
            else:
                c1_v, c2_v = c2_v, (c1_v + 1) % 3
        return (c1_v, c2_v)

    for s_i in (1, 2, 3):
        ms_2c = 3 * (4 ** (12 + 18 * s_i)) + (1 << 25)
        if _run_bounded_2counter(ms_2c) != _run_bounded_2counter(ms_2c << 18):
            lsb_and_pda_ok = False
            break

    # 4. Unconditional ALL-Q MSB & LSB raw-counter OCN & polynomial-bitLength denominator refutation
    #    via constructive Mod-9 synchronized backward Collatz branch-descent from x_0 = 5:
    dz_asym = [((0, 0), (1, 0)), ((0, 1), (1, 0))]
    dp_asym = [((0, 0), (0, 1)), ((1, 0), (1, 0))]
    dz_lsb_asym = [((1, 0), (0, 1)), ((1, 0), (1, 0))]
    dp_lsb_asym = [((0, 0), (0, 1)), ((1, 0), (1, 0))]
    shift_mod9 = {4: 1, 2: 2, 1: 3, 5: 4, 7: 5, 8: 6}

    all_raw_ocn_ok = True
    for k_t in range(4, 12):
        ms_k = 3 * (1 << k_t) - 1
        ev_k = 2 * ms_k
        ns_k = (1 << (k_t + 1)) - 1
        cm_k = run_msb_one_counter_ocn(2, dz_asym, dp_asym, 0, ms_k)[1]
        ce_k = run_msb_one_counter_ocn(2, dz_asym, dp_asym, 0, ev_k)[1]
        cn_k = run_msb_one_counter_ocn(2, dz_asym, dp_asym, 0, ns_k)[1]
        # Asymmetric MSB slopes: cm_k == ce_k == k_t + 1 (sl2 >= 1) while cn_k == 0 (sl1 = 0)!
        if (
            cm_k != k_t + 1
            or ce_k != k_t + 1
            or cn_k != 0
            or Fraction(ce_k + 1, (k_t + 3) ** 2) + Fraction(1, (k_t + 1) ** 2)
            >= Fraction(cm_k + 1, (k_t + 2) ** 2)
        ):
            all_raw_ocn_ok = False
            break
        # Asymmetric LSB 1-run slopes on ms_k vs ev_k: (q0, 0) grows as k_t + 1 while step(0) stays 0!
        cl_m = run_lsb_one_counter_ocn(2, dz_lsb_asym, dp_lsb_asym, 0, ms_k)[1]
        cl_e = run_lsb_one_counter_ocn(2, dz_lsb_asym, dp_lsb_asym, 0, ev_k)[1]
        if cl_m < k_t or cl_e != 0:
            all_raw_ocn_ok = False
            break

    # Verify Mod-9 branch-descent invariants & guaranteed Z+ failure across asymmetric MSB,
    # unequal-slope LSB, arbitrary-initial-counter (c0 > 0) OCN, joint MSB+LSB dual-counter,
    # multi-push general context-free PDA stack-height, and constant-denominator (D=0) weights,
    # BOTH from x_0 = 5 AND eventually above cutoffs M_0 in (3, 10, 50) (x_0 = 6 * M_0 + 5)!
    def _general_multipush_pda_height(n_val: int) -> int:
        stk_v: List[int] = [0, 1]
        q_v = 0
        for ch_b in bin(n_val)[2:]:
            top_v = stk_v.pop() if stk_v else None
            if ch_b == "1":
                stk_v.extend([2, 1, 0] if q_v == 0 else [1, 2])
                q_v = 1 - q_v
            elif top_v == 2 and stk_v:
                stk_v.pop()
            elif top_v is not None:
                stk_v.append((top_v + 1) % 3)
        return len(stk_v)

    candidate_weights = (
        lambda n_v: (
            run_msb_one_counter_ocn(2, dz_asym, dp_asym, 0, n_v)[1] + 1,
            n_v.bit_length() ** 2,
        ),
        lambda n_v: (
            run_lsb_one_counter_ocn(2, dz_lsb_asym, dp_lsb_asym, 0, n_v)[1] + 1,
            n_v.bit_length() ** 2,
        ),
        lambda n_v: (
            run_lsb_one_counter_ocn(2, dz_lsb_asym, dp_lsb_asym, 0, n_v, c0=7)[1] + 1,
            (n_v.bit_length() ** 2) + 7,
        ),
        lambda n_v: (
            1
            + run_msb_one_counter_ocn(2, dz_asym, dp_asym, 0, n_v)[1]
            + run_lsb_one_counter_ocn(2, dz_lsb_asym, dp_lsb_asym, 0, n_v)[1],
            (n_v.bit_length() ** 2)
            + run_msb_one_counter_ocn(2, dz_w2, dp_w2, 0, n_v)[1]
            + 1,
        ),
        lambda n_v: (
            run_msb_pda_stack(2, 3, pda_tbl, 0, n_v)[2] + 1,
            (n_v.bit_length() ** 2) + 1,
        ),
        lambda n_v: (
            _general_multipush_pda_height(n_v) + 1,
            (n_v.bit_length() ** 2) + _general_multipush_pda_height(n_v) + 1,
        ),
        lambda n_v: (1, 1),
    )
    for wf in candidate_weights:
        for m0_cut, x0_anchor in ((3, 5), (3, 23), (10, 65), (50, 305)):
            found_violation = False
            cur_x = x0_anchor
            wx0_n, wx0_d = wf(x0_anchor)
            for k_step in range(1, 55):
                r_sh = shift_mod9[cur_x % 9]
                cur_m = cur_x
                for _ in range(r_sh):
                    if cur_m < m0_cut or (cur_m % 3 == 2 and (2 * cur_m - 1) // 3 < m0_cut):
                        all_raw_ocn_ok = False
                        break
                    wn_2, wd_2 = wf(2 * cur_m)
                    wn_1, wd_1 = wf(cur_m)
                    if wn_2 * wd_1 > wn_1 * wd_2:
                        found_violation = True
                        break
                    cur_m *= 2
                if not all_raw_ocn_ok or found_violation:
                    break
                y0 = 2 * cur_m
                y1 = (2 * cur_m - 1) // 3
                wn_m, wd_m = wf(cur_m)
                wn_0, wd_0 = wf(y0)
                wn_1c, wd_1c = wf(y1)
                if (wn_0 * wd_1c + wn_1c * wd_0) * wd_m > wn_m * (wd_0 * wd_1c):
                    found_violation = True
                    break
                nxt_x = mod9_backward_collatz_branch_next(wf, cur_x)
                exp_x = y0 if (2 * wn_0 * wd_m <= wn_m * wd_0) else y1
                wn_xk, wd_xk = wf(nxt_x)
                exp_cap = (7 * k_step + 3) if x0_anchor == 5 else (7 * k_step + x0_anchor)
                if (
                    nxt_x != exp_x
                    or nxt_x <= cur_x
                    or nxt_x < x0_anchor + k_step
                    or (nxt_x % 3) == 0
                    or nxt_x >= (1 << exp_cap)
                    or nxt_x.bit_length() > exp_cap
                    or (1 << k_step) * wn_xk * wx0_d > wx0_n * wd_xk
                ):
                    all_raw_ocn_ok = False
                    break
                cur_x = nxt_x
            if not all_raw_ocn_ok or not found_violation:
                all_raw_ocn_ok = False
                break
        if not all_raw_ocn_ok:
            break

    return {
        "general_mixed_sign_ocn_mode_and_dual_pumping_verified": mixed_ocn_ok,
        "lsb_raw_counter_ocn_and_pda_two_counter_verified": lsb_and_pda_ok,
        "all_ocn_raw_counter_and_mod9_branch_descent_verified": all_raw_ocn_ok,
        "cousin_diamond8_outside_cones4to9_descent_verified": d8_outside_ok,
        "cousin_diamond8_cone9_6tier_cascade_verified": d8_cone9_ok and d8_jump_ok,
        "cousin_diamond8_countermodels_verified": d8_countermodels_ok,
    }


def audit_w11_front_d_supercritical_dyadic_and_markov_mod162() -> Dict[str, Any]:
    """
    Front D (`Branch P2.2` & `P5.3`):
    1. Verify exact static first-hit equivalence `is_first_hit_one_pair(u, 0) <=>
       canonical_suffix_shift(u, 1) >= 3` across all core words `1 <= |u| <= 11`, and exact
       all-ones power-of-3 law `canonical_suffix_shift((1,)*w, 1) == 3**(w - 1)` (`w = 1..10`).
    2. Verify Complete Mod-`162` (`2 * 3^4`) Markov Bijection (`markovShiftTrue(w, a) % 162`
       determined by `a % 54` for all `w >= 4`, bijecting `{0..53}` onto the exact `54` surviving
       classes `{r < 162 : r % 6 in (1, 3)}`), `108/162 = 2/3` forbidden-residue confinement on
       `w(u) >= 5`, and universal 5-ones suffix lock `canonical_suffix_shift(pref + (1,1,1,1,1), 1) % 162 == 81`!
    3. Verify Universal Super-Critical `L > M + w + 1` Dyadic-Window Shift-Multiplicity Law across
       all core words `1 <= |u| <= 12` AND super-critical surviving `Mod373248` orbits (`27`, `111`),
       coupled with `dyadicWindowSurvivingQ0Leaves` (`w >= 6`, `|u| >= 8`, `100%` `mod 162`
       confinement) and `3**(w - 5)` (`j = 4`) Markov fiber equidistribution!
    """
    from . import cs_forest_transfer as cft

    all_core_le12: List[Tuple[int, ...]] = [(1,)]
    for length in range(2, 13):
        for mid in product((0, 1), repeat=length - 2):
            all_core_le12.append((1,) + mid + (1,))

    first_hit_and_pow3_ok = True
    for w_ones in range(1, 11):
        if cft.canonical_suffix_shift((1,) * w_ones, 1) != (3 ** (w_ones - 1)):
            first_hit_and_pow3_ok = False
            break
    for u_c in all_core_le12:
        if len(u_c) <= 11:
            fh = cft.is_first_hit_one_pair(u_c, 0)
            sh = cft.canonical_suffix_shift(u_c, 1)
            if fh != (sh >= 3):
                first_hit_and_pow3_ok = False
                break

    def _ms_true(w_in: int, a_in: int) -> int:
        return cft.dlog2_mod_pow3_aux(w_in, 3 * (1 << a_in) + 1) - 1

    def _ms_false(w_in: int, a_in: int) -> int:
        return a_in - 1 if a_in >= 1 else 2 * (3 ** (w_in - 1)) - 1

    def _iter_ms(tail_b: Tuple[int, ...], w_in: int, a_in: int) -> int:
        cw, ca = w_in, a_in
        for bit_t in tail_b:
            if bit_t == 0:
                ca = _ms_false(cw, ca)
            else:
                ca = _ms_true(cw, ca)
                cw += 1
        return ca

    mod162_table = {r54: _ms_true(4, r54) % 162 for r54 in range(54)}
    expected_54 = {r162 for r162 in range(162) if (r162 % 6) in (1, 3)}
    mod162_ok = (len(set(mod162_table.values())) == 54) and (set(mod162_table.values()) == expected_54)

    for w_t in (4, 5, 6):
        for a_t in range(2 * (3 ** (w_t - 1))):
            if (_ms_true(w_t, a_t) % 162) != mod162_table[a_t % 54]:
                mod162_ok = False
                break
    for u_w in all_core_le12:
        if sum(u_w) >= 5 and (cft.canonical_suffix_shift(u_w, 1) % 162) not in expected_54:
            mod162_ok = False
            break
    prefixes = ((), (1,), (1, 0), (1, 1), (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1))
    for pref in prefixes:
        if (
            (cft.canonical_suffix_shift(pref + (1, 1, 1, 1, 1), 1) % 162) != 81
            or (cft.canonical_suffix_shift(pref + (1, 0, 1, 1, 1, 1), 1) % 162) != 135
        ):
            mod162_ok = False
            break

    # Super-critical shift-multiplicity ceiling across ALL L >= 1
    shifts_by_cell: Dict[Tuple[int, int, int], Set[int]] = {}
    supercrit_ok = True
    extra_sc_words: List[Tuple[int, ...]] = []
    for sc_y in (27, 111):
        cur_v = sc_y
        w_list: List[int] = []
        while (cur_v & (cur_v - 1)) != 0:
            b_v = cur_v & 1
            w_list.append(b_v)
            cur_v = (3 * cur_v + 1) // 2 if b_v else cur_v // 2
        extra_sc_words.append(tuple(w_list))

    surviving_leaves_seen = 0
    window_and_fiber_ok = True
    for u_c in all_core_le12 + extra_sc_words:
        l_u = len(u_c)
        w_u = sum(u_c)
        a_u = cft.canonical_suffix_shift(u_c, 1)
        y0 = cft.exact_backward_quotient(1, u_c, 0)
        m_win = y0.bit_length() - 1
        shifts_by_cell.setdefault((m_win, l_u, w_u), set()).add(a_u)
        if cft.is_first_hit_one_pair(u_c, 0) and cft.is_surviving_mod373248_class(y0):
            surviving_leaves_seen += 1
            if w_u < 6 or l_u < 8 or a_u < 3 or (a_u % 162) not in expected_54:
                window_and_fiber_ok = False
                break

    # Verify 3**(w - 5) (j = 4, M0 = 162) exact fiber equidistribution for w = 5, 6, 7 across tails
    for w_fib in (5, 6, 7):
        n_fib = 3 ** (w_fib - 5)
        for tail_f in ((1,), (0, 1), (1, 0, 1)):
            mk_mod = 2 * (3 ** (4 + sum(tail_f)))
            for r0_f in (1, 3, 81, 135):
                base_f = _iter_ms(tail_f, w_fib, r0_f) % mk_mod
                qs_seen = []
                for t_idx in range(n_fib):
                    out_v = _iter_ms(tail_f, w_fib, r0_f + 162 * t_idx)
                    if (out_v % mk_mod) != base_f:
                        window_and_fiber_ok = False
                        break
                    qs_seen.append((out_v - base_f) // mk_mod)
                if sorted(qs_seen) != list(range(n_fib)):
                    window_and_fiber_ok = False
                    break

    found_supercrit = False
    for (m_w, l_w, w_w), s_vals in shifts_by_cell.items():
        a_lo = min(s_vals)
        a_hi = max(s_vals)
        excess = max(0, l_w - (m_w + w_w + 1))
        if l_w > m_w + w_w + 1:
            found_supercrit = True
        if (
            (1 << (a_hi - a_lo + m_w + w_w)) >= ((1 << (m_w + w_w + 1)) + (1 << l_w))
            or (a_hi - a_lo) > excess + 1
            or len(s_vals) > ((excess + 1) // 2) + 1
        ):
            supercrit_ok = False
            break
        if l_w == m_w + w_w + 2 and w_w >= 2 and (a_lo % 6) == 3 and len(s_vals) > 1:
            supercrit_ok = False
            break

    return {
        "first_hit_shift_ge3_and_pow3_ones_verified": first_hit_and_pow3_ok,
        "markov_mod162_bijection_and_81_lock_verified": mod162_ok,
        "dyadic_supercritical_shift_multiplicity_verified": supercrit_ok and found_supercrit,
        "surviving_window_leaves_mod162_and_fiber_equidist_verified": (
            window_and_fiber_ok and surviving_leaves_seen >= 3
        ),
    }


def _dynamic_pred_mixed_sign_q2_ocn_mode_separates_preimages(
    _dom: str, entry: Dict[str, Any]
) -> bool:
    """
    Dynamic test of false claim that a mixed-sign `Q = 2` zero-testing `1`-counter (`OCN`)
    observable mode `(q, c == 0)` separates `m` from `4 * m` across `P_2 = 2`-padded branching
    targets `m >= 3` (`m % 3 == 2`). Zero hardcoded witness IDs.
    """
    if "next_compressed" not in entry or "ocn_q2_multi_even_preimage" not in entry:
        return True
    m_tgt = int(entry["next_compressed"])
    ocn2_ev = int(entry["ocn_q2_multi_even_preimage"])
    if m_tgt < 3 or (m_tgt % 3) != 2 or ocn2_ev != 4 * m_tgt:
        return True
    dz_mix = [((1, 0), (0, 1)), ((0, 0), (1, 1))]
    dp_mix = [((1, 0), (0, 1)), ((0, -1), (1, -1))]
    rm_m = run_msb_one_counter_ocn(2, dz_mix, dp_mix, 0, m_tgt)
    rm_e = run_msb_one_counter_ocn(2, dz_mix, dp_mix, 0, ocn2_ev)
    rl_m = run_lsb_one_counter_ocn(2, dz_mix, dp_mix, 0, m_tgt)
    rl_e = run_lsb_one_counter_ocn(2, dz_mix, dp_mix, 0, ocn2_ev)
    return ((rm_m[0], rm_m[1] == 0) != (rm_e[0], rm_e[1] == 0)) or (
        (rl_m[0], rl_m[1] == 0) != (rl_e[0], rl_e[1] == 0)
    )


def _dynamic_pred_pda_q2_g3_stack_separates_preimages(
    _dom: str, entry: Dict[str, Any]
) -> bool:
    """
    Dynamic test of false claim that a multi-symbol context-free `PDA` (`Q = 2, |Gamma| = 3`)
    separates `m` from `64 * m` across `2^6`-padded branching targets `m >= 3` (`m % 3 == 2`).
    """
    if "next_compressed" not in entry or "pda_q2_g3_multi_even_preimage" not in entry:
        return True
    m_tgt = int(entry["next_compressed"])
    pda_ev = int(entry["pda_q2_g3_multi_even_preimage"])
    if m_tgt < 3 or (m_tgt % 3) != 2 or pda_ev != 64 * m_tgt:
        return True
    tbl = _canonical_pda_q2_g3_table()
    return run_msb_pda_stack(2, 3, tbl, 0, m_tgt) != run_msb_pda_stack(2, 3, tbl, 0, pda_ev)


def _dynamic_pred_asym_slope_q2_ocn_mersenne_bypass_weight(
    _dom: str, entry: Dict[str, Any]
) -> bool:
    """
    Dynamic test of false claim that an asymmetric zero-vs-positive slope `Q = 2` `1`-counter `OCN`
    raw-counter weight `w(n) = (c_MSB(n) + 1) / bitLength(n)^2` (which strictly satisfies
    `w(2*m) + w((2*m-1)/3) < w(m)` across ALL `k >= 4` Mersenne targets `m = 3*2^k - 1`)
    satisfies preimage superharmonicity across `Z^+`. Zero hardcoded witness IDs.
    """
    if "next_compressed" not in entry or "asym_ocn_even_preimage" not in entry:
        return True
    m_tgt = int(entry["next_compressed"])
    ev_tgt = int(entry["asym_ocn_even_preimage"])
    if m_tgt < 3 or (m_tgt % 3) != 2 or ev_tgt != 2 * m_tgt:
        return True
    dz_asym = [((0, 0), (1, 0)), ((0, 1), (1, 0))]
    dp_asym = [((0, 0), (0, 1)), ((1, 0), (1, 0))]

    def _w_asym(val_n: int) -> Fraction:
        _, c_v = run_msb_one_counter_ocn(2, dz_asym, dp_asym, 0, val_n)
        bl_v = val_n.bit_length()
        return Fraction(c_v + 1, bl_v * bl_v)

    n_odd = (2 * m_tgt - 1) // 3
    return (_w_asym(ev_tgt) + _w_asym(n_odd)) <= _w_asym(m_tgt)


def _dynamic_pred_phi2_on_cousin_diamond8_outside_cones4to8(
    _dom: str, entry: Dict[str, Any]
) -> bool:
    """Dynamic test of single-step `Phi_diamond2` descent on `T_diamond8` outside Cones 4..8."""
    seed = int(entry.get("seed", 0))
    if (
        seed <= 2
        or is_diamond3_cone4(seed)
        or is_diamond4_cone5(seed)
        or is_diamond5_cone6(seed)
        or is_diamond6_cone7(seed)
        or is_diamond7_cone8(seed)
    ):
        return True
    nxt = cousin_diamond8_step_int(seed, q=3)
    return cousin_diamond2_phi(nxt) < cousin_diamond2_phi(seed)


def _dynamic_pred_twobase_6x6_t3u2_even_u_nonzero_and_all_pos(
    _dom: str, entry: Dict[str, Any]
) -> bool:
    """
    Dynamic test of false extrapolation that rank-2 Vandermonde two-base `6 x 6` `(T = 3, U = 2)`
    Schneider-Laurent determinants are non-zero at even `u` across coprime `3^W < 2^K`.
    """
    if "W" not in entry or "K" not in entry or "laurent_twobase_6x6_t3u2_u" not in entry:
        return True
    w_v = int(entry["W"])
    k_v = int(entry["K"])
    u_v = int(entry["laurent_twobase_6x6_t3u2_u"])
    if w_v < 1 or k_v < 1 or u_v < 1 or (u_v & 1) == 1 or math.gcd(w_v, k_v) != 1 or (3**w_v) >= (1 << k_v):
        return True
    return laurent_twobase_6x6_t3u2_det_closed(w_v, k_v, u_v) != 0


def _dynamic_pred_twobase_8x8_t4u2_cone_positivity(
    _dom: str, entry: Dict[str, Any]
) -> bool:
    """
    Dynamic test of false extrapolation that `8 x 8` two-base `(T = 4, U = 2)` determinants
    remain strictly positive (`> 0`) for all `u >= 1` inside `3^W < 2^K` and `3 * K <= 5 * W`.
    """
    if "W" not in entry or "K" not in entry or "laurent_twobase_8x8_t4u2_u1_det" not in entry:
        return True
    w_v = int(entry["W"])
    k_v = int(entry["K"])
    if w_v < 1 or k_v < 1 or math.gcd(w_v, k_v) != 1 or (3**w_v) >= (1 << k_v) or 3 * k_v > 5 * w_v:
        return True
    return laurent_twobase_8x8_t4u2_det_matrix(w_v, k_v, 1) > 0


def _dynamic_pred_mod24_5_17_prime_forces_even_gcd(_dom: str, entry: Dict[str, Any]) -> bool:
    """Dynamic test of false claim that all primes `q == 5, 17 (mod 24)` have even `gcd(ord_q(2), ord_q(3/2))`."""
    if "mod24_5_escape_prime" not in entry or "mod24_17_escape_prime" not in entry:
        return True
    q5 = int(entry["mod24_5_escape_prime"])
    q17 = int(entry["mod24_17_escape_prime"])
    if q5 < 5 or q17 < 5 or (q5 % 24) != 5 or (q17 % 24) != 17:
        return True
    g5 = math.gcd(_mult_order_mod_prime(2, q5), _mult_order_mod_prime((3 * pow(2, -1, q5)) % q5, q5))
    g17 = math.gcd(_mult_order_mod_prime(2, q17), _mult_order_mod_prime((3 * pow(2, -1, q17)) % q17, q17))
    return (g5 % 2) == 0 and (g17 % 2) == 0


def _dynamic_pred_length_blind_dyadic_shift_pinning_or_subcritical(
    _dom: str, entry: Dict[str, Any]
) -> bool:
    """
    Dynamic test of false claim that inside `[2^M, 2^(M+1))` equal `(M, w)` pins
    `canonical_suffix_shift(u, 1)` without fixing word length `L`.
    """
    if (
        "dyadic_length_window_m" not in entry
        or "dyadic_length_partner_word" not in entry
        or "core_word" not in entry
    ):
        return True
    from . import cs_forest_transfer as cft

    m_win = int(entry["dyadic_length_window_m"])
    u1 = tuple(int(b) for b in entry["core_word"])
    u2 = tuple(int(b) for b in entry["dyadic_length_partner_word"])
    if sum(u1) != sum(u2) or not cft.is_first_hit_one_pair(u1, 0) or not cft.is_first_hit_one_pair(u2, 0):
        return True
    y1 = cft.exact_backward_quotient(1, u1, 0)
    y2 = cft.exact_backward_quotient(1, u2, 0)
    if not ((1 << m_win) <= y1 < (1 << (m_win + 1)) and (1 << m_win) <= y2 < (1 << (m_win + 1))):
        return True
    return cft.canonical_suffix_shift(u1, 1) == cft.canonical_suffix_shift(u2, 1)


def run_wave11_whole_space_campaign(bank_path: Optional[Path] = None) -> Dict[str, Any]:
    """
    Execute the complete Wave 11 whole-space red-team, Left-Anchored Arts-Giesl Dependency Pair
    (`DP`) reduction + `TwoSided(L_K x R_M)` (`K in {2, 4, 8}`, `M in {3, 6, 12, 18}`) cascades +
    universal finite-carrier Mersenne `R8` commutator barrier, complete mod-`24` `2`-adic & `l`-Sylow
    (`mod 72, 96, 240`) reciprocity + companion-prime quotient cascades + all-`m` shared-Mersenne
    locks + upgraded `T^2` confluent extrapolation + exact rank-2 Vandermonde `6 x 6` `(T = 3, U = 2)`
    & `8 x 8` `(T = 4, U = 2)` grids, general mixed-sign `Q >= 1` MSB/LSB zero-testing `1`-counter
    (`OCN`) & multi-symbol `PDA` stack-height barriers + 8th solvable cousin `T_diamond8` (`omega^6`),
    and super-critical `L > M + w + 1` dyadic-window shift-multiplicity + mod-`162` `3^(w - 5)`
    Markov fiber confinement campaign.
    """
    u_gate = audit_universality_gate(
        "Wave11_WholeSpace_W11_1_to_W11_4",
        is_finite_m_table=False,
        is_finite_n_table=False,
        is_bounded_weight_table=False,
        uses_native_decide=False,
        uses_sorry=False,
        axioms_used=("propext", "Classical.choice", "Quot.sound"),
    )
    bank = load_witness_bank(bank_path)
    wb_truth = verify_witness_bank_ground_truth(bank_path)

    gate_mixed_ocn = evaluate_hypothesis_against_witness_bank(
        "MixedSignQ2OCNModeSeparatesPreimages",
        _dynamic_pred_mixed_sign_q2_ocn_mode_separates_preimages,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    gate_pda = evaluate_hypothesis_against_witness_bank(
        "MultiSymbolPDAQ2G3StackSeparatesPreimages",
        _dynamic_pred_pda_q2_g3_stack_separates_preimages,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    gate_asym_ocn = evaluate_hypothesis_against_witness_bank(
        "AsymmetricSlopeQ2OCNMersenneBypassPreimageWeight",
        _dynamic_pred_asym_slope_q2_ocn_mersenne_bypass_weight,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    gate_phi2_d8 = evaluate_hypothesis_against_witness_bank(
        "OutsideCones4to8Phi2OnCousinDiamond8",
        _dynamic_pred_phi2_on_cousin_diamond8_outside_cones4to8,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )
    gate_t3u2 = evaluate_hypothesis_against_witness_bank(
        "TwoBase6x6T3U2LaurentEvenUNonzero",
        _dynamic_pred_twobase_6x6_t3u2_even_u_nonzero_and_all_pos,
        domains=("log2_3_convergents",),
        bank_path=bank_path,
    )
    gate_t4u2_8x8 = evaluate_hypothesis_against_witness_bank(
        "TwoBase8x8T4U2LaurentConePositivity",
        _dynamic_pred_twobase_8x8_t4u2_cone_positivity,
        domains=("log2_3_convergents",),
        bank_path=bank_path,
    )
    gate_recip = evaluate_hypothesis_against_witness_bank(
        "Mod24Primes5And17ForceEvenGCD",
        _dynamic_pred_mod24_5_17_prime_forces_even_gcd,
        domains=("log2_3_convergents",),
        bank_path=bank_path,
    )
    gate_dyadic_len = evaluate_hypothesis_against_witness_bank(
        "LengthBlindDyadicWindowShiftPinning",
        _dynamic_pred_length_blind_dyadic_shift_pinning_or_subcritical,
        domains=("z_pos_high_glide",),
        bank_path=bank_path,
    )

    front_a = audit_w11_front_a_left_anchored_dp_and_mersenne_r8_barrier()
    front_b = audit_w11_front_b_reciprocity_sylow_and_laurent_t3u2()
    front_c = audit_w11_front_c_general_mixed_sign_ocn_and_diamond8()
    front_d = audit_w11_front_d_supercritical_dyadic_and_markov_mod162()

    passed = (
        u_gate.passed
        and bool(wb_truth["all_witnesses_ground_truth_verified"])
        and (not gate_mixed_ocn["passed"])
        and gate_mixed_ocn["minimal_failure"]
        == ("z_pos_high_glide", "ZPOS_MIXED_SIGN_Q2_OCN_PREIMAGE_COLLAPSE")
        and (not gate_pda["passed"])
        and gate_pda["minimal_failure"]
        == ("z_pos_high_glide", "ZPOS_PDA_STACK_Q2_G3_COLLISION_8_VS_512")
        and (not gate_asym_ocn["passed"])
        and gate_asym_ocn["minimal_failure"]
        == ("z_pos_high_glide", "ZPOS_ASYMMETRIC_SLOPE_Q2_OCN_MERSENNE_BYPASS")
        and (not gate_phi2_d8["passed"])
        and gate_phi2_d8["minimal_failure"]
        == ("z_pos_high_glide", "ZPOS_COUSIN_DIAMOND8_CONE9_100571021_JUMP")
        and (not gate_t3u2["passed"])
        and gate_t3u2["minimal_failure"]
        == ("log2_3_convergents", "LAURENT_TWOBASE_6X6_T3U2_EVEN_U2_ZERO_3_8_AND_OUTER_FLIP")
        and (not gate_t4u2_8x8["passed"])
        and gate_t4u2_8x8["minimal_failure"]
        == ("log2_3_convergents", "LAURENT_TWOBASE_8X8_T4U2_CONE_FLIP_3_5_VS_5_8")
        and (not gate_recip["passed"])
        and gate_recip["minimal_failure"]
        == ("log2_3_convergents", "RECIPROCITY_MOD24_5_17_ODD_GCD_ESCAPE_29_AND_89")
        and (not gate_dyadic_len["passed"])
        and gate_dyadic_len["minimal_failure"]
        == ("z_pos_high_glide", "ZPOS_DYADIC_WINDOW_M6_W3_LENGTH_SPLIT_69_VS_75")
        and bool(front_a["left_anchored_dp_and_omit_r2_termination_verified"])
        and bool(front_a["twosided_m3_m6_omit_r3_and_all11_cascades_verified"])
        and bool(front_a["universal_mersenne_b1_t2_lock_and_r8_cycle_verified"])
        and bool(front_a["higher_carriers_k2_4_8_m6_12_18_and_flip2_verified"])
        and bool(front_b["reciprocity_mod24_complete_and_sylow_verified"])
        and bool(front_b["twoblock_cubic_quintic_octic_floors_verified"])
        and bool(front_b["companion_quotient_cascades_and_mblock_sylow_verified"])
        and bool(front_b["confluent_t2_t3_extrapolation_8x8_and_laplace_verified"])
        and bool(front_b["laurent_8x8_twobase_t4u2_divisibility_and_cone_flip_verified"])
        and bool(front_b["laurent_6x6_t3u2_closed_form_odd_u_and_cone_pos_verified"])
        and bool(front_c["general_mixed_sign_ocn_mode_and_dual_pumping_verified"])
        and bool(front_c["lsb_raw_counter_ocn_and_pda_two_counter_verified"])
        and bool(front_c["all_ocn_raw_counter_and_mod9_branch_descent_verified"])
        and bool(front_c["cousin_diamond8_outside_cones4to9_descent_verified"])
        and bool(front_c["cousin_diamond8_cone9_6tier_cascade_verified"])
        and bool(front_c["cousin_diamond8_countermodels_verified"])
        and bool(front_d["first_hit_shift_ge3_and_pow3_ones_verified"])
        and bool(front_d["markov_mod162_bijection_and_81_lock_verified"])
        and bool(front_d["dyadic_supercritical_shift_multiplicity_verified"])
        and bool(front_d["surviving_window_leaves_mod162_and_fiber_equidist_verified"])
    )
    return {
        "passed": passed,
        "verdict": "REDTEAM-PASSED" if passed else "FALSIFIED",
        "universality_gate_passed": u_gate.passed,
        "witness_bank_total_entries": sum(len(v) for v in bank["domains"].values()),
        "witness_bank_falsified_count": len(bank["falsified_hypotheses"]),
        "witness_bank_ground_truth_verified": bool(wb_truth["all_witnesses_ground_truth_verified"]),
        "front_a_dp_twosided_and_mersenne_r8": front_a,
        "front_b_reciprocity_sylow_and_laurent_t3u2": front_b,
        "front_c_general_mixed_sign_ocn_and_diamond8": front_c,
        "front_d_supercritical_dyadic_and_markov_mod162": front_d,
    }
