"""
Exact 2-Adic, Parity-Vector, and Affine Carry Formalism for the Collatz Map.

Implements:
1. Compressed Collatz map T(n) and Syracuse map S(n) trajectories and stopping times:
   - Glide / stopping time sigma(n) = inf {k >= 1 : T^k(n) < n}
   - Coefficient stopping time tau(n) = inf {k >= 1 : 3^{w_k(n)} < 2^k}
   - Total stopping time sigma_inf(n) = inf {k >= 0 : T^k(n) = 1}
2. The Terras-Lagarias Parity Homeomorphism Phi_k : Z / 2^k Z -> {0, 1}^k and its
   exact Hensel-lifting inverse Phi_k^{-1} : {0, 1}^k -> Z / 2^k Z.
3. Exact Affine Decomposition T^k(n) = (3^w n + C_k(v)) / 2^k and the Odd-Step
   Valuation Identity:
       C_k(v) = sum_{m=1}^w 3^{w - m} 2^{j_m}
   where 0 <= j_1 < j_2 < ... < j_w < k are the indices of the odd steps.
4. Extremal Carry Bounds:
   - Universal bounds: 3^w - 2^w <= C_k(v) <= 2^{k-w}(3^w - 2^w)
   - Surviving-Path Carry Bound (for any prefix surviving up to step k):
     C_k(v) <= w * 3^{w-1} - (3^{w-1} - 1) // 2
5. Bohm-Sontacchi 2-Adic Rational Cycle Reconstruction:
   n_cycle(v) = C_k(v) / (2^k - 3^w) in Q intersect Z_{(2)}.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, List, Optional, Sequence, Tuple


def collatz_compressed_step(n: int) -> int:
    """Compute one step of the compressed Collatz map T(n)."""
    if n % 2 == 0:
        return n // 2
    return (3 * n + 1) // 2


def syracuse_step(n: int) -> Tuple[int, int]:
    """
    Compute one step of the Syracuse map S(n) on odd integers.
    Returns (S(n), a) where 3n + 1 = 2^a * S(n) with S(n) odd.
    """
    if n % 2 == 0:
        raise ValueError(f"Syracuse map requires an odd integer, got {n}")
    val = 3 * n + 1
    a = (val & -val).bit_length() - 1
    return val >> a, a


@dataclass(frozen=True)
class TrajectoryAnalysis:
    """Complete trajectory and stopping-time analysis for a starting integer n."""

    n: int
    orbit: Tuple[int, ...]
    parity_vector: Tuple[int, ...]
    stopping_time_sigma: Optional[int]
    coeff_stopping_time_tau: Optional[int]
    total_stopping_time: int
    max_excursion: int


def analyze_trajectory(n: int, max_steps: int = 10000) -> TrajectoryAnalysis:
    """Compute the compressed Collatz trajectory and all three stopping times for n >= 1."""
    if n < 1:
        raise ValueError(f"n must be >= 1, got {n}")
    if n == 1:
        return TrajectoryAnalysis(
            n=1,
            orbit=(1,),
            parity_vector=(),
            stopping_time_sigma=None,
            coeff_stopping_time_tau=None,
            total_stopping_time=0,
            max_excursion=1,
        )

    orbit: List[int] = [n]
    parities: List[int] = []
    curr = n
    sigma: Optional[int] = None
    tau: Optional[int] = None
    w = 0
    max_val = n

    for step in range(1, max_steps + 1):
        p = curr & 1
        parities.append(p)
        w += p
        curr = (3 * curr + 1) >> 1 if p else curr >> 1
        orbit.append(curr)
        if curr > max_val:
            max_val = curr
        if sigma is None and curr < n:
            sigma = step
        if tau is None and (3**w) < (1 << step):
            tau = step
        if curr == 1 and sigma is not None and tau is not None:
            break

    total_stop = orbit.index(1) if 1 in orbit else -1
    return TrajectoryAnalysis(
        n=n,
        orbit=tuple(orbit),
        parity_vector=tuple(parities),
        stopping_time_sigma=sigma,
        coeff_stopping_time_tau=tau,
        total_stopping_time=total_stop,
        max_excursion=max_val,
    )


def parity_vector(n: int, k: int) -> Tuple[int, ...]:
    """
    Compute the parity vector Phi_k(n) = (n mod 2, T(n) mod 2, ..., T^{k-1}(n) mod 2).
    """
    if k < 0:
        raise ValueError(f"k must be >= 0, got {k}")
    curr = n
    vec: List[int] = []
    for _ in range(k):
        p = curr & 1
        vec.append(p)
        curr = (3 * curr + 1) >> 1 if p else curr >> 1
    return tuple(vec)


def affine_parameters(v: Sequence[int]) -> Tuple[int, int, int]:
    """
    Given a parity vector v in {0, 1}^k, return (k, w, C_k(v)) such that for any
    n with parity_vector(n, k) == v:
        T^k(n) = (3^w * n + C_k(v)) / 2^k.

    Recurrence:
        C_0 = 0
        C_{j+1} = 3 * C_j + 2^j   if v_j == 1
        C_{j+1} = C_j             if v_j == 0
    """
    k = len(v)
    w = 0
    carry = 0
    for j, bit in enumerate(v):
        if bit not in (0, 1):
            raise ValueError(f"Parity vector entries must be 0 or 1, got {bit}")
        if bit == 1:
            w += 1
            carry = 3 * carry + (1 << j)
    return k, w, carry


def carry_via_odd_indices(v: Sequence[int]) -> int:
    """
    Compute C_k(v) via the Odd-Step Valuation Identity:
        C_k(v) = sum_{m=1}^w 3^{w - m} * 2^{j_m}
    where 0 <= j_1 < j_2 < ... < j_w < k are the 0-based indices of the 1s in v.
    """
    odd_indices = [j for j, bit in enumerate(v) if bit == 1]
    w = len(odd_indices)
    return sum((3 ** (w - 1 - idx)) * (1 << j_m) for idx, j_m in enumerate(odd_indices))


def inverse_parity_vector(v: Sequence[int]) -> int:
    """
    Compute the unique residue r in {0, 1, ..., 2^k - 1} such that
    Phi_k(r) == tuple(v) via Hensel lifting / modular inversion.

    Since T^k(n) = (3^w * n + C_k(v)) / 2^k is an integer iff
        3^w * n + C_k(v) == 0 (mod 2^k),
    the unique solution modulo 2^k is:
        r = (-C_k(v) * (3^w)^{-1}) mod 2^k.
    """
    k, w, carry = affine_parameters(v)
    if k == 0:
        return 0
    mod = 1 << k
    inv_3w = pow(3, -w, mod)
    return (-carry * inv_3w) % mod


def verify_parity_bijection(k: int) -> Dict[str, object]:
    """
    Exhaustively verify that Phi_k : Z / 2^k Z -> {0, 1}^k is a bijection
    and that inverse_parity_vector(v) is its exact two-sided inverse.
    """
    mod = 1 << k
    seen_vectors = set()
    for r in range(mod):
        v = parity_vector(r, k)
        seen_vectors.add(v)
        r_recovered = inverse_parity_vector(v)
        if r_recovered != r:
            raise AssertionError(f"Hensel inverse mismatch at r={r}, v={v}: got {r_recovered}")
        _, w, carry = affine_parameters(v)
        num = (3**w) * r + carry
        if num % mod != 0:
            raise AssertionError(f"Affine divisibility failed at r={r}")
    return {
        "k": k,
        "modulus": mod,
        "distinct_vectors": len(seen_vectors),
        "is_bijection": len(seen_vectors) == mod,
    }


def extremal_carry_bounds(k: int, w: int) -> Tuple[int, int]:
    """
    Return the universal lower and upper bounds (C_min(k, w), C_max(k, w)) for C_k(v)
    over all parity vectors v in {0, 1}^k of weight w:
        C_min(k, w) = 3^w - 2^w               (attained uniquely by 1^w 0^{k-w})
        C_max(k, w) = 2^{k-w} * (3^w - 2^w)   (attained uniquely by 0^{k-w} 1^w)
    """
    if not (0 <= w <= k):
        raise ValueError(f"Require 0 <= w <= k, got k={k}, w={w}")
    base = (3**w) - (1 << w)
    return base, (1 << (k - w)) * base


def surviving_path_carry_bound(w: int) -> int:
    """
    Return the exact upper bound on C_k(v) for ANY parity vector v of weight w
    that is coefficient-surviving up to its last odd step (i.e. 3^{w_j} > 2^j
    for all 1 <= j <= j_w):
        C_k(v) <= w * 3^{w-1} - (3^{w-1} - 1) // 2.
    """
    if w <= 0:
        return 0
    p3 = 3 ** (w - 1)
    return w * p3 - (p3 - 1) // 2


def is_coefficient_surviving_prefix(v: Sequence[int], strict_until_end: bool = True) -> bool:
    """
    Check whether the parity vector v satisfies 3^{w_j} > 2^j for all prefixes j.
    If strict_until_end is False, checks 1 <= j < len(v) (allowing step k to be the stopping step).
    """
    w = 0
    limit = len(v) if strict_until_end else max(0, len(v) - 1)
    for j in range(1, limit + 1):
        w += v[j - 1]
        if (3**w) <= (1 << j):
            return False
    return True


@dataclass(frozen=True)
class RationalCycleOrbit:
    """
    Exact 2-adic / rational periodic orbit associated with a repeating parity vector v^infty.
    By Bohm-Sontacchi (1978) and Lagarias (1985), every periodic parity vector v in {0, 1}^k
    has a unique periodic orbit in Q intersect Z_2 generated by:
        n_0 = C_k(v) / (2^k - 3^w).
    """

    parity_vector: Tuple[int, ...]
    k: int
    w: int
    carry: int
    denominator_gap: int
    n0: Fraction
    orbit: Tuple[Fraction, ...]
    is_positive_integer_cycle: bool


def rational_cycle_for_parity_vector(v: Sequence[int]) -> RationalCycleOrbit:
    """
    Compute the unique rational periodic orbit in Q intersect Z_2 with period v.
    """
    k, w, carry = affine_parameters(v)
    if k == 0:
        raise ValueError("Parity vector must be non-empty")
    denom = (1 << k) - (3**w)
    n0 = Fraction(carry, denom)
    orbit: List[Fraction] = []
    curr = n0
    for bit in v:
        orbit.append(curr)
        if bit == 0:
            curr = curr / 2
        else:
            curr = (3 * curr + 1) / 2
    if curr != n0:
        raise AssertionError(f"Cycle closure failed: ended at {curr} != {n0}")
    is_pos_int = n0.denominator == 1 and n0.numerator > 0
    return RationalCycleOrbit(
        parity_vector=tuple(v),
        k=k,
        w=w,
        carry=carry,
        denominator_gap=denom,
        n0=n0,
        orbit=tuple(orbit),
        is_positive_integer_cycle=is_pos_int,
    )
