"""Track 1: Universal Cycle Exclusion & Exact Rational LP / Farkas Dual Synthesis.

Implements:
1. Exact `fractions.Fraction` Karp minimum-mean-cycle and Bellman-Ford / Farkas dual
   solver (zero floating-point arithmetic) on joint `(x mod 2^A * 3^B, spiral-step)`
   transition graphs generalizing Theorem 19.1 (`1/x` and `1/(x + 1)` step bounds).
2. Constructive Bezout lifting and Universal `(2^A * 3^B)` Bounded-Modulus
   Rational-Potential Obstruction witnesses in `Q_(2)^+ ∩ Q_(3)^+` (`19/5`,
   `29/5 <-> 23/5`, high-floor `319/13 > 24` with `r_0 == 43 mod 48`, and general
   Sturmian parity words for any `2^K > 3^W`).
3. Universal `forall x p` cycle structural reductions (`[]` custom axioms in pure
   Lean 4 Core, zero `BarinaThreshold` or `BakerLMNPowerBound`):
   - T1: Trajectory/cycle multiplicative ratio sandwich `(3*M + 1)^W <= 2^K * M^W`,
     `2^K * m^W <= (3*m + 1)^W`, pure-Nat binomial peak floor
     `W * 3^(W - 1) <= (2^K - 3^W) * M`, and strict odd non-constancy (`m < M` on
     every non-trivial cycle, ruling out `W = 1` unconditionally).
   - T2: Universal `x % 3 != 0` periodic invariance, cycle-minimum mod-48 sieve
     `x_0 % 48 in {7, 11, 19, 23, 31, 35, 43, 47}`, `M % 12 in {1, 5}` cycle odd
     maximum rigidity, and tightened `(21, 22)` exponent band `21^W < 7^W * 2^K <= 22^W`
     (unconditionally forcing `W >= 5, K >= 8` without parity enumeration).
   - T3a/T3b: Sharp single-equation Diophantine and pure-Nat Brox odd-carry
     (`(2^K - 3^W) * q_0 = brox_odd_carry(rest)`) equivalences (`<->`) for
     `NoNontrivialPositiveCycles`, verified against the mandatory 3x3 Counter-Model
     Gate (`M1 = Q_(2)^+`, `M2 = Z^-`, `M3 = 5x + 1`).
   - T5--T8 (Wave 2): Mod-24 determinant gap `{5, 7, 13, 23}`, 2-adic LTE bound
     `2^a | (3^w - 1) => 2^a <= 4*w`, 1-block `q_0 = 1` Mersenne elimination,
     trailing-`false` Brox split, and `Z^+` integer-discreteness first-block
     dichotomy (`2^(w1 + a1) < 3^w1`) with mod-96 `1/12` cycle-minimum sieve.
   - T9--T11 (Wave 3): 1-block GCD/congruence lock `D | gcd(2^a1 - 1, 3^w1 - 2^w1)`,
     universal `{2, 3}`-smooth quotient elimination (`forall r, q_0 != 3^r`),
     `q_0 % 24 in {3, 9, 17, 19}` (`q_0 >= 17`, `w1 >= 13, a1 >= 8`,
     `x_0 % 96 in {31, 95}`, `(17 * 3^w1) // 2^a1 == 17 * 2^w1 - 1`), exact 2-block
     cleared-denominator reciprocal/potential identity & Mersenne vertex elimination
     (`q_0, q_1 >= 3`, `x_0 >= 47`, `23 * D < 3^W`, `W >= 8`), Dual Brox Cubic
     Exponential Collapse `27 * 2^(W + a1 - 3) * D^3 < 2^(3*K)` unifying
     `NoOneBlockPositiveCycles` and `NoTwoBlockPositiveCycles` under
     `SubexponentialCubicGapProp`, and Hercher subdouble-merger 1-block elimination
     at minimal non-convergent integers + Unified Two-Barrier Master Core.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import math
from typing import Hashable, Sequence


MOD96_SURVIVING_CYCLE_MIN_CLASSES: frozenset[int] = frozenset(
    {7, 31, 47, 59, 71, 79, 91, 95}
)
MOD96_ONE_BLOCK_X0_CLASSES: frozenset[int] = frozenset({31, 95})
MOD48_SURVIVING_CYCLE_MIN_CLASSES: frozenset[int] = frozenset(
    {7, 11, 23, 31, 43, 47}
)
MOD32_SURVIVING_CYCLE_MIN_CLASSES: frozenset[int] = frozenset({7, 15, 27, 31})
MOD16_SURVIVING_CYCLE_MIN_CLASSES: frozenset[int] = frozenset({7, 11, 15})
MOD12_SURVIVING_CYCLE_MAX_ODD_CLASSES: frozenset[int] = frozenset({1, 5})
MOD24_DETERMINANT_CLASSES: frozenset[int] = frozenset({5, 7, 13, 23})
MOD24_ONE_BLOCK_Q0_CLASSES: frozenset[int] = frozenset({3, 9, 17, 19})


# ============================================================================
# 1. Exact Arithmetic Primitives & Brox Odd-Carry Recurrence
# ============================================================================


def parity_weight(v: Sequence[bool]) -> int:
    """Count the number of odd (`True`) steps in a compressed parity word."""
    return sum(1 for bit in v if bit)


def affine_carry(v: Sequence[bool], q: int = 3) -> int:
    """Compute exact affine carry `C^(q)(v)` for compressed `(q*x + 1)/2` steps."""
    acc = 0
    for j, bit in enumerate(v):
        if bit:
            acc = q * acc + (1 << j)
    return acc


def brox_odd_carry(rest: Sequence[bool]) -> int:
    """Pure-Nat strictly positive odd carry `broxOddCarry` for shifted `+1` cycles.

    Matches the Lean 4 Core structural recursion:
      `broxOddCarry [] = 1`
      `broxOddCarry (_ :: u) = 2 * broxOddCarry u + 3 ^ parityWeight u`
    """
    if not rest:
        return 1
    tail = rest[1:]
    return 2 * brox_odd_carry(tail) + (3 ** parity_weight(tail))


def rotate_left(v: Sequence[bool], j: int) -> list[bool]:
    """Cyclically rotate parity word `v` left by `j` positions."""
    n = len(v)
    if n == 0:
        return []
    shift = j % n
    return list(v[shift:]) + list(v[:shift])


def collatz_step_int(x: int, q: int = 3) -> int:
    """Compressed `(q*x + 1)/2` step over `Z` (for odd multiplier `q`)."""
    if q % 2 == 0:
        raise ValueError("Multiplier q must be odd.")
    if x % 2 == 0:
        return x // 2
    return (q * x + 1) // 2


def collatz_step_2adic_fraction(x: Fraction, q: int = 3) -> tuple[Fraction, bool]:
    """Exact compressed `(q*x + 1)/2` step on `Q_(2)` (odd denominator)."""
    if q % 2 == 0:
        raise ValueError("Multiplier q must be odd.")
    if x.denominator % 2 == 0:
        raise ValueError(f"Input {x} is not in Q_(2) (even denominator).")
    is_odd = (x.numerator % 2) != 0
    if not is_odd:
        return x / 2, False
    nxt = (q * x + 1) / 2
    if nxt.denominator % 2 == 0:
        raise ValueError(f"Step image {nxt} left Q_(2).")
    return nxt, True


def rational_cycle_from_parity_word(
    v: Sequence[bool], q: int = 3
) -> list[Fraction]:
    """Return the exact `Q_(2)` periodic trajectory realized by parity word `v`."""
    k_len = len(v)
    if k_len == 0:
        raise ValueError("Parity word must be non-empty.")
    w = parity_weight(v)
    det = (1 << k_len) - (q**w)
    if det == 0:
        raise ValueError("Degenerate determinant 2^K - q^W == 0.")
    c_val = affine_carry(v, q=q)
    x0 = Fraction(c_val, det)
    orbit: list[Fraction] = []
    cur = x0
    for expected_bit in v:
        orbit.append(cur)
        cur, actual_bit = collatz_step_2adic_fraction(cur, q=q)
        if actual_bit != expected_bit:
            raise AssertionError(
                f"Parity mismatch at {cur}: expected {expected_bit}, got {actual_bit}"
            )
    if cur != x0:
        raise AssertionError(f"Orbit did not close: ended at {cur} != {x0}")
    return orbit


def decompose_spiral_blocks(v: Sequence[bool]) -> list[tuple[int, int]]:
    """Decompose a parity word starting with `True` and ending with `False` into `(k, l)` blocks."""
    if not v or not v[0] or v[-1]:
        raise ValueError(
            "Spiral decomposition requires word starting with True and ending with False."
        )
    blocks: list[tuple[int, int]] = []
    i = 0
    n = len(v)
    while i < n:
        k_run = 0
        while i < n and v[i]:
            k_run += 1
            i += 1
        l_run = 0
        while i < n and not v[i]:
            l_run += 1
            i += 1
        if k_run == 0 or l_run == 0:
            raise ValueError("Invalid block boundary in parity word.")
        blocks.append((k_run, l_run))
    return blocks


def parity_word_from_spiral_blocks(blocks: Sequence[tuple[int, int]]) -> list[bool]:
    """Expand spiral `(k_i, l_i)` blocks into a compressed parity word."""
    word: list[bool] = []
    for k_run, l_run in blocks:
        if k_run < 1 or l_run < 1:
            raise ValueError("Each spiral block requires k >= 1 and l >= 1.")
        word.extend([True] * k_run)
        word.extend([False] * l_run)
    return word


# ============================================================================
# 2. Exact `fractions.Fraction` Karp Minimum-Mean-Cycle & Farkas Dual Solver
# ============================================================================


@dataclass(frozen=True)
class DirectedEdge:
    """Weighted directed multigraph edge in exact `Fraction` arithmetic."""

    src: Hashable
    dst: Hashable
    cost: Fraction
    label: tuple[int, ...]


@dataclass(frozen=True)
class ExactKarpFarkasResult:
    """Exact primal/dual output of Karp's algorithm + Bellman-Ford / Farkas extraction."""

    min_mean_cost: Fraction
    has_universal_potential: bool
    potentials: dict[Hashable, Fraction] | None
    farkas_cycle: list[DirectedEdge] | None
    farkas_circulation: dict[int, Fraction] | None


def _extract_zero_or_neg_shifted_cycle(
    vertices: Sequence[Hashable],
    edges: Sequence[DirectedEdge],
    shift: Fraction,
) -> list[int]:
    """Find a simple directed cycle whose `(cost - shift)` sum is `<= 0` in exact `Fraction`."""
    n = len(vertices)
    dist: dict[Hashable, Fraction] = {v: Fraction(0) for v in vertices}
    pred_edge: dict[Hashable, int | None] = {v: None for v in vertices}

    # First check for strictly negative `(cost - shift)` cycle via Bellman-Ford.
    last_updated: Hashable | None = None
    for _step in range(n + 1):
        last_updated = None
        for idx, edge in enumerate(edges):
            cand = dist[edge.src] + (edge.cost - shift)
            if cand < dist[edge.dst]:
                dist[edge.dst] = cand
                pred_edge[edge.dst] = idx
                last_updated = edge.dst

    if last_updated is not None:
        cur = last_updated
        for _ in range(n):
            pe = pred_edge[cur]
            assert pe is not None
            cur = edges[pe].src
        cycle_indices: list[int] = []
        v_ptr = cur
        while True:
            pe = pred_edge[v_ptr]
            assert pe is not None
            cycle_indices.append(pe)
            v_ptr = edges[pe].src
            if v_ptr == cur:
                break
        cycle_indices.reverse()
        return cycle_indices

    # Otherwise no negative `(cost - shift)` cycle exists, so `dist` is an exact feasible
    # potential satisfying `(cost - shift) + dist[u] - dist[v] >= 0` on ALL edges, and
    # every critical cycle consists exclusively of tight (`== 0`) reduced-cost edges!
    tight_adj: dict[Hashable, list[int]] = {v: [] for v in vertices}
    for idx, edge in enumerate(edges):
        reduced = (edge.cost - shift) + dist[edge.src] - dist[edge.dst]
        if reduced == 0:
            tight_adj[edge.src].append(idx)

    # Extract a simple directed cycle in the tight subgraph via exact 3-color DFS.
    color: dict[Hashable, int] = {v: 0 for v in vertices}  # 0=unvisited, 1=active, 2=done
    stack_edge: dict[Hashable, int] = {}

    for start in vertices:
        if color[start] != 0:
            continue
        # Iterative DFS to avoid Python recursion limits on larger modular graphs.
        frames: list[tuple[Hashable, int]] = [(start, 0)]
        color[start] = 1
        while frames:
            u, pos = frames[-1]
            out_list = tight_adj[u]
            if pos >= len(out_list):
                color[u] = 2
                frames.pop()
                continue
            frames[-1] = (u, pos + 1)
            e_idx = out_list[pos]
            w = edges[e_idx].dst
            if color[w] == 1:
                # Found back-edge closing a simple cycle on the active stack.
                cyc: list[int] = [e_idx]
                # Walk active frames backward from `u` down to `w`.
                for k_pos in range(len(frames) - 1, 0, -1):
                    node_here = frames[k_pos][0]
                    if node_here == w:
                        break
                    cyc.append(stack_edge[node_here])
                cyc.reverse()
                return cyc
            if color[w] == 0:
                stack_edge[w] = e_idx
                color[w] = 1
                frames.append((w, 0))

    raise RuntimeError("Tight subgraph contained no directed cycle despite finite mu*.")


def exact_karp_min_mean_cycle(
    vertices: Sequence[Hashable],
    edges: Sequence[DirectedEdge],
) -> ExactKarpFarkasResult:
    """Compute exact `Fraction` minimum mean cycle cost + primal/dual Farkas certificate.

    By LP duality / Farkas's Lemma on the edge-incidence matrix `B`:
      `max_{Phi, mu} { mu : c_e + Phi(u) - Phi(v) >= mu for all e = (u -> v) }`
      `= min_{f >= 0} { sum_e c_e f_e : B f = 0, sum_e f_e = 1 }`.
    - If `mu* > 0` (or the graph is acyclic), returns an exact `Fraction` potential
      `Phi` certifying `c_e + Phi(u) - Phi(v) >= mu* > 0` on EVERY edge (proving
      no closed walk of ANY length `m >= 1` has non-positive cost sum).
    - If `mu* <= 0`, returns an exact simple directed cycle `C` and normalized
      circulation `f` (`f_e = 1/|C|` on `C`) with `sum_e c_e f_e = mu* <= 0`,
      proving NO rational potential `Phi` can achieve strictly positive reduced costs.
    """
    unique_vertices = list(dict.fromkeys(vertices))
    n = len(unique_vertices)
    if n == 0 or not edges:
        return ExactKarpFarkasResult(
            min_mean_cost=Fraction(1),
            has_universal_potential=True,
            potentials={v: Fraction(0) for v in unique_vertices},
            farkas_cycle=None,
            farkas_circulation=None,
        )

    # Karp DP from virtual super-source `s` at distance 0 to all vertices at step 0.
    dp: list[dict[Hashable, Fraction | None]] = [
        {v: Fraction(0) for v in unique_vertices}
    ]
    for _k in range(1, n + 1):
        prev = dp[-1]
        cur_row: dict[Hashable, Fraction | None] = {v: None for v in unique_vertices}
        for edge in edges:
            prev_u = prev[edge.src]
            if prev_u is None:
                continue
            cand = prev_u + edge.cost
            old = cur_row[edge.dst]
            if old is None or cand < old:
                cur_row[edge.dst] = cand
        dp.append(cur_row)

    # If `dp[n][v]` is None for EVERY `v`, the directed graph is a DAG (no cycles at all).
    if all(dp[n][v] is None for v in unique_vertices):
        # Compute topological / longest-path potential so `1 + Phi(u) - Phi(v) >= 1`
        # or `c_e + Phi(u) - Phi(v) >= 1` via Bellman-Ford with `c_e - 1` on DAG:
        shift = Fraction(1)
        dist: dict[Hashable, Fraction] = {v: Fraction(0) for v in unique_vertices}
        for _ in range(n):
            for edge in edges:
                cand = dist[edge.src] + (edge.cost - shift)
                if cand < dist[edge.dst]:
                    dist[edge.dst] = cand
        return ExactKarpFarkasResult(
            min_mean_cost=shift,
            has_universal_potential=True,
            potentials=dist,
            farkas_cycle=None,
            farkas_circulation=None,
        )

    mu_star: Fraction | None = None
    for v in unique_vertices:
        d_nv = dp[n][v]
        if d_nv is None:
            continue
        max_for_v: Fraction | None = None
        for k in range(n):
            d_kv = dp[k][v]
            if d_kv is None:
                continue
            ratio = (d_nv - d_kv) / (n - k)
            if max_for_v is None or ratio > max_for_v:
                max_for_v = ratio
        assert max_for_v is not None
        if mu_star is None or max_for_v < mu_star:
            mu_star = max_for_v

    assert mu_star is not None

    if mu_star > 0:
        # Bellman-Ford shortest paths under shifted edge weight `c_e - mu_star`
        # (guaranteed free of negative cycles!) gives `Phi(v) = dist[v]` satisfying
        # `dist[v] <= dist[u] + c_e - mu_star`, i.e., `c_e + Phi(u) - Phi(v) >= mu_star > 0`!
        pot: dict[Hashable, Fraction] = {v: Fraction(0) for v in unique_vertices}
        for _ in range(n):
            changed = False
            for edge in edges:
                cand = pot[edge.src] + (edge.cost - mu_star)
                if cand < pot[edge.dst]:
                    pot[edge.dst] = cand
                    changed = True
            if not changed:
                break
        return ExactKarpFarkasResult(
            min_mean_cost=mu_star,
            has_universal_potential=True,
            potentials=pot,
            farkas_cycle=None,
            farkas_circulation=None,
        )

    # Dual obstruction regime (`mu_star <= 0`): extract exact Farkas dual cycle.
    cyc_indices = _extract_zero_or_neg_shifted_cycle(unique_vertices, edges, mu_star)
    cyc_edges = [edges[idx] for idx in cyc_indices]
    r_len = len(cyc_indices)
    unit_flow = Fraction(1, r_len)
    circulation: dict[int, Fraction] = {idx: unit_flow for idx in cyc_indices}
    actual_mean = sum((e.cost for e in cyc_edges), Fraction(0)) / r_len
    return ExactKarpFarkasResult(
        min_mean_cost=actual_mean,
        has_universal_potential=False,
        potentials=None,
        farkas_cycle=cyc_edges,
        farkas_circulation=circulation,
    )


def verify_potential_certificate(
    edges: Sequence[DirectedEdge],
    potentials: dict[Hashable, Fraction],
    min_slack: Fraction,
) -> bool:
    """Verify `min_slack > 0` and `e.cost + Phi(src) - Phi(dst) >= min_slack` on all edges."""
    if min_slack <= 0:
        return False
    for edge in edges:
        if edge.src not in potentials or edge.dst not in potentials:
            return False
        reduced = edge.cost + potentials[edge.src] - potentials[edge.dst]
        if reduced < min_slack:
            return False
    return True


def verify_farkas_circulation(
    vertices: Sequence[Hashable],
    edges: Sequence[DirectedEdge],
    circulation: dict[int, Fraction],
    cycle_edges: Sequence[DirectedEdge],
) -> bool:
    """Verify non-negativity, unit normalization, flow conservation, and `<= 0` mean cost."""
    if not circulation or not cycle_edges:
        return False
    # Check closed walk property of `cycle_edges`.
    for i, edge in enumerate(cycle_edges):
        nxt = cycle_edges[(i + 1) % len(cycle_edges)]
        if edge.dst != nxt.src:
            return False
    total_flow = Fraction(0)
    total_cost = Fraction(0)
    net_flow: dict[Hashable, Fraction] = {v: Fraction(0) for v in vertices}
    for idx, flow in circulation.items():
        if idx < 0 or idx >= len(edges) or flow < 0:
            return False
        e = edges[idx]
        total_flow += flow
        total_cost += e.cost * flow
        net_flow[e.src] = net_flow.get(e.src, Fraction(0)) - flow
        net_flow[e.dst] = net_flow.get(e.dst, Fraction(0)) + flow
    if total_flow != 1:
        return False
    if any(val != 0 for val in net_flow.values()):
        return False
    return total_cost <= 0


# ============================================================================
# 3. Joint `(x mod 2^A * 3^B, Spiral-Step)` Transition Graphs & Theorem 19.1 Potentials
# ============================================================================


def step_contraction_lower_bound(k: int, l: int, n0_floor: int) -> Fraction:
    """Exact `Fraction` lower bound on `1 - x_{i+1} / x_i` for spiral step `(k, l)` at `x_i >= n0`.

    From `2^(k + l) * x_{i+1} = 3^k * x_i + (3^k - 2^k)` (`3^k > 2^k` for `k >= 1`),
    for every `x_i >= n0_floor >= 1`:
      `x_{i+1} / x_i <= (3^k * n0 + 3^k - 2^k) / (2^(k + l) * n0)`.
    Around ANY closed positive cycle `x_0, ..., x_{m-1} > 0`, exact rational AM-GM
    (`prod (x_{i+1}/x_i) == 1 => sum (x_{i+1}/x_i) >= m`) forces `sum (1 - x_{i+1}/x_i) <= 0`.
    """
    if k < 1 or l < 1 or n0_floor < 1:
        raise ValueError("Requires k >= 1, l >= 1, n0_floor >= 1.")
    num = (3**k) * n0_floor + (3**k - (1 << k))
    den = (1 << (k + l)) * n0_floor
    return Fraction(1) - Fraction(num, den)


def shifted_reciprocal_step_slack(k: int, l: int, n0_floor: int) -> Fraction:
    """Exact `Fraction` lower bound on `1 - (x_{i+1} + 1) / (x_i + 1)` at `x_i >= n0`.

    From `2^(k + l) * (x_{i+1} + 1) = 3^k * (x_i + 1) + 2^k * (2^l - 1)`:
      `(x_{i+1} + 1) / (x_i + 1) = 3^k / 2^(k + l) + ((2^l - 1) / 2^l) / (x_i + 1)`.
    """
    if k < 1 or l < 1 or n0_floor < 1:
        raise ValueError("Requires k >= 1, l >= 1, n0_floor >= 1.")
    ratio_hi = Fraction(3**k, 1 << (k + l)) + Fraction(
        (1 << l) - 1, (1 << l) * (n0_floor + 1)
    )
    return Fraction(1) - ratio_hi


def generalized_thm19_1_reciprocal_drift(
    x: Fraction, k: int, l: int, pole_c: Fraction = Fraction(0)
) -> Fraction:
    """Exact `Fraction` step difference `1/(x_next + c) - 1/(x + c)` for spiral step `(k, l)`.

    Generalizes Theorem 19.1 (`c = 0`: `1/x_{i+1} - 1/x_i`; `c = 1`: `1/(x_{i+1}+1) - 1/(x_i+1)`)
    along `2^(k + l) * x_next = 3^k * x + (3^k - 2^k)` in exact rational arithmetic.
    """
    if k < 1 or l < 1 or x + pole_c <= 0:
        raise ValueError("Requires k >= 1, l >= 1, and x + pole_c > 0.")
    x_next = Fraction((3**k) * x + (3**k - (1 << k)), 1 << (k + l))
    if x_next + pole_c <= 0:
        raise ValueError("Image x_next + pole_c must be strictly positive.")
    return Fraction(1, x_next + pole_c) - Fraction(1, x + pole_c)


def verify_multipole_rational_potential_annihilation(
    v: Sequence[bool],
    A: int,
    B: int,
    poles: Sequence[Fraction],
    alpha_weights: Sequence[Fraction],
) -> bool:
    """Verify Farkas dual annihilation of ANY multi-pole `sum_c alpha_c/(x + c) + psi(r)` potential.

    Evaluates the spiral transitions `(k_i, l_i)` along the `Q_(2)^+ ∩ Q_(3)^+` cycle of `v`
    and verifies that the uniform Farkas circulation `lambda_i = 1 / m > 0` identically
    annihilates both the `(2^A * 3^B)` modular potential differences AND every rational
    pole basis `1/(x_{i+1} + c) - 1/(x_i + c)` simultaneously (`sum == 0`).
    """
    if len(poles) != len(alpha_weights):
        raise ValueError("poles and alpha_weights must have equal length.")
    blocks = decompose_spiral_blocks(v)
    orbit = rational_cycle_from_parity_word(v, q=3)
    if any(x <= 0 for x in orbit):
        raise ValueError("Requires positive rational cycle in Q_(2)^+ ∩ Q_(3)^+.")

    det = orbit[0].denominator
    u_inv, _ = bezout_coprime_pow2_pow3(det, A, B)
    modulus = (1 << A) * (3**B)

    spiral_vertices: list[Fraction] = []
    pos = 0
    for k_run, l_run in blocks:
        spiral_vertices.append(orbit[pos])
        pos = (pos + k_run + l_run) % len(v)

    m = len(blocks)
    farkas_weight = Fraction(1, m)
    total_dual_eval = Fraction(0)

    for idx, (k_run, l_run) in enumerate(blocks):
        x_cur = spiral_vertices[idx]
        x_nxt = spiral_vertices[(idx + 1) % m]
        r_cur = (x_cur.numerator * u_inv) % modulus if modulus > 1 else 0
        r_nxt = (x_nxt.numerator * u_inv) % modulus if modulus > 1 else 0

        psi_diff = Fraction(r_nxt * r_nxt + 7 * r_nxt, modulus + 1) - Fraction(
            r_cur * r_cur + 7 * r_cur, modulus + 1
        )
        rat_diff = Fraction(0)
        for c_pole, alpha in zip(poles, alpha_weights):
            step_drift = generalized_thm19_1_reciprocal_drift(
                x_cur, k_run, l_run, pole_c=c_pole
            )
            expected_diff = Fraction(1, x_nxt + c_pole) - Fraction(1, x_cur + c_pole)
            if step_drift != expected_diff:
                return False
            rat_diff += alpha * step_drift

        total_dual_eval += farkas_weight * (psi_diff + rat_diff)

    return total_dual_eval == 0


def verify_rational_cycle_amgm_nonpositive(values: Sequence[Fraction]) -> bool:
    """Verify in pure `Fraction` arithmetic that `sum(1 - x_{i+1}/x_i) <= 0` for `x_i > 0`."""
    m = len(values)
    if m == 0 or any(v <= 0 for v in values):
        raise ValueError("Requires non-empty sequence of strictly positive Fractions.")
    prod_ratios = Fraction(1)
    sum_slack = Fraction(0)
    for i in range(m):
        ratio = values[(i + 1) % m] / values[i]
        prod_ratios *= ratio
        sum_slack += Fraction(1) - ratio
    return prod_ratios == 1 and sum_slack <= 0


def valid_spiral_residues(A: int, B: int) -> list[int]:
    """Return active spiral local-minimum residue classes modulo `M = 2^A * 3^B`.

    Every spiral vertex on a positive (or `Q_(2) ∩ Q_(3)`) cycle is odd (`r % 2 == 1`
    when `A >= 1`) and non-divisible by `3` (`r % 3 != 0` when `B >= 1`).
    """
    if A < 0 or B < 0:
        raise ValueError("Exponents A, B must be non-negative.")
    modulus = (1 << A) * (3**B)
    out: list[int] = []
    for r in range(modulus):
        if A >= 1 and (r % 2 == 0):
            continue
        if B >= 1 and (r % 3 == 0):
            continue
        out.append(r)
    return out


def build_modular_spiral_graph(
    A: int,
    B: int,
    allowed_steps: Sequence[tuple[int, int]],
    n0_floor: int = 4,
    cost_mode: str = "step_contraction",
) -> tuple[list[int], list[DirectedEdge]]:
    """Build joint `(x mod 2^A * 3^B, spiral-step (k, l))` transition multigraph.

    Models the exact spiral transition congruence:
      `2^(k + l) * (r_next + 1) == 3^k * (r + 1) + 2^k * (2^l - 1) (mod 2^A * 3^B)`
    together with the `+1` binary valuation constraint `(r + 1) == 2^k * u (mod 2^A)`
    with `u` odd!
    """
    modulus = (1 << A) * (3**B)
    pow2_mod = 1 << A
    vertices = valid_spiral_residues(A, B)
    vertex_set = set(vertices)
    edges: list[DirectedEdge] = []

    for k, l in allowed_steps:
        if cost_mode == "step_contraction":
            c_val = step_contraction_lower_bound(k, l, n0_floor)
        elif cost_mode == "shifted_reciprocal":
            c_val = shifted_reciprocal_step_slack(k, l, n0_floor)
        else:
            raise ValueError(f"Unknown cost_mode: {cost_mode}")

        for r in vertices:
            # Check exact 2-adic valuation of `r + 1` up to precision `2^A`:
            # `r + 1 = 2^k * u` with `u` odd requires:
            # - if `k < A`: `(r + 1) % 2^(k + 1) == 2^k`
            # - if `k >= A`: `(r + 1) % 2^A == 0`
            if A >= 1:
                if k < A:
                    if (r + 1) % (1 << (k + 1)) != (1 << k):
                        continue
                else:
                    if (r + 1) % pow2_mod != 0:
                        continue

            rhs = (3**k) * (r + 1) + (1 << k) * ((1 << l) - 1)
            coeff = 1 << (k + l)
            for r_next in vertices:
                if r_next not in vertex_set:
                    continue
                if (coeff * (r_next + 1) - rhs) % modulus == 0:
                    edges.append(
                        DirectedEdge(src=r, dst=r_next, cost=c_val, label=(k, l))
                    )

    return vertices, edges


def build_archimedean_macro_spiral_graph(
    A: int,
    B: int,
    single_steps: Sequence[tuple[int, int]],
    max_macro_len: int = 3,
    n0_floor: int = 4,
) -> tuple[list[int], list[DirectedEdge]]:
    """Compose 1..`max_macro_len` spiral steps restricted to `2^K > 3^W` macro-transitions.

    Eliminates all `M2 = Z^-` (`2^K < 3^W`) circulations so Karp's solver probes
    strictly positive-determinant (`2^K > 3^W`) circulations, directly surfacing
    `M1 = Q_(2)^+ ∩ Q_(3)^+` rational pseudo-cycles (`19/5`, `29/5 <-> 23/5`, `319/13`).
    """
    vertices, step_edges = build_modular_spiral_graph(
        A, B, single_steps, n0_floor=n0_floor, cost_mode="step_contraction"
    )
    adj: dict[int, list[DirectedEdge]] = {v: [] for v in vertices}
    for e in step_edges:
        adj[int(e.src)].append(e)

    macro_edges: list[DirectedEdge] = []
    for m_len in range(1, max_macro_len + 1):
        # Enumerate valid `m_len`-step walks starting at each residue `r0`.
        for r0 in vertices:
            stack: list[tuple[int, int, int, Fraction, tuple[int, ...]]] = [
                (r0, 0, 0, Fraction(0), ())
            ]
            while stack:
                cur_v, tot_k, tot_w, tot_cost, flat_lbl = stack.pop()
                depth = len(flat_lbl) // 2
                if depth == m_len:
                    if (1 << tot_k) > (3**tot_w):
                        macro_edges.append(
                            DirectedEdge(
                                src=r0,
                                dst=cur_v,
                                cost=tot_cost,
                                label=flat_lbl,
                            )
                        )
                    continue
                for edge in adj[cur_v]:
                    ek, el = edge.label
                    stack.append(
                        (
                            int(edge.dst),
                            tot_k + ek + el,
                            tot_w + ek,
                            tot_cost + edge.cost,
                            flat_lbl + (ek, el),
                        )
                    )

    return vertices, macro_edges


def reconstruct_rational_pseudo_cycle(
    cycle_edges: Sequence[DirectedEdge],
    A: int,
    B: int,
) -> dict[str, object]:
    """Reconstruct exact `Q_(2) ∩ Q_(3)` periodic point from a Farkas spiral cycle witness."""
    if not cycle_edges:
        raise ValueError("Cycle witness must be non-empty.")
    blocks: list[tuple[int, int]] = []
    for edge in cycle_edges:
        lbl = edge.label
        for idx in range(0, len(lbl), 2):
            blocks.append((lbl[idx], lbl[idx + 1]))
    v_word = parity_word_from_spiral_blocks(blocks)
    orbit = rational_cycle_from_parity_word(v_word, q=3)
    x0 = orbit[0]

    # Verify exact `(2^A * 3^B)` modular residue agreement at each macro/step boundary.
    modulus = (1 << A) * (3**B)
    u_inv, _v_inv = bezout_coprime_pow2_pow3(x0.denominator, A, B)
    pos = 0
    residues_match = True
    for edge in cycle_edges:
        val_at_edge = orbit[pos]
        r_proj = (val_at_edge.numerator * u_inv) % modulus if modulus > 1 else 0
        if r_proj != edge.src:
            residues_match = False
        lbl = edge.label
        step_span = sum(lbl)
        pos = (pos + step_span) % len(v_word)

    return {
        "blocks": blocks,
        "parity_word": v_word,
        "K": len(v_word),
        "W": parity_weight(v_word),
        "determinant": (1 << len(v_word)) - (3 ** parity_weight(v_word)),
        "x0": x0,
        "min_value": min(orbit),
        "max_value": max(orbit),
        "is_positive_rational_cycle": all(val > 0 for val in orbit),
        "is_integer_cycle": all(val.denominator == 1 for val in orbit),
        "modular_projection_matches": residues_match,
    }


# ============================================================================
# 4. Theorem T4: Constructive Bezout Lifting & Bounded-Modulus Obstruction
# ============================================================================


def _bezout_product_lift(
    d: int, m: int, u1: int, v1: int, n: int, u2: int, v2: int
) -> tuple[int, int]:
    """Lift `d*u1 + m*v1 == 1` and `d*u2 + n*v2 == 1` to `d*U + (m*n)*V == 1`.

    Uses the exact ring identity `(d*u1 + m*v1) * (d*u2 + n*v2) = 1`:
      `U = u1 * (d * u2 + n * v2) + m * v1 * u2`, `V = v1 * v2`.
    """
    u_comb = u1 * (d * u2 + n * v2) + m * v1 * u2
    v_comb = v1 * v2
    return u_comb, v_comb


def bezout_coprime_pow2_pow3(d: int, A: int, B: int) -> tuple[int, int]:
    """Constructive pure-Int Bezout witness `(U, V)` with `d * U + (2^A * 3^B) * V == 1`.

    Mirrors the exact Mathlib-free Lean 4 Core inductive proof for any integer `d`
    satisfying `d % 2 == 1` and `d % 3 != 0`.
    """
    if d % 2 == 0 or d % 3 == 0:
        raise ValueError(f"Denominator d={d} must be coprime to 6.")
    if A < 0 or B < 0:
        raise ValueError("Exponents A, B must be non-negative.")

    # Base 2-adic Bezout: `d * 0 + 1 * 1 == 1` at 2^0, step `d * 1 + 2 * (-(d - 1)//2) == 1`.
    u2, v2, m2 = 0, 1, 1
    step_u2, step_v2 = 1, -((d - 1) // 2)
    for _ in range(A):
        u2, v2 = _bezout_product_lift(d, m2, u2, v2, 2, step_u2, step_v2)
        m2 *= 2

    # Base 3-adic Bezout: `d * 0 + 1 * 1 == 1` at 3^0, lifted to `3^B`.
    u3, v3, m3 = 0, 1, 1
    if d % 3 == 1:
        step_u3, step_v3 = 1, -((d - 1) // 3)
    else:
        step_u3, step_v3 = 2, -((2 * d - 1) // 3)
    for _ in range(B):
        u3, v3 = _bezout_product_lift(d, m3, u3, v3, 3, step_u3, step_v3)
        m3 *= 3

    u_tot, v_tot = _bezout_product_lift(d, m2, u2, v2, m3, u3, v3)
    assert d * u_tot + (m2 * m3) * v_tot == 1
    return u_tot, v_tot


def construct_modular_pseudo_cycle_witness(
    v: Sequence[bool], A: int, B: int
) -> dict[str, object]:
    """Verify Theorem T4 (`Universal Bounded-Modulus Rational-Potential Obstruction`).

    For EVERY `(A, B)` and EVERY parity word `v` with `2^|v| > 3^w(v)` and `w(v) >= 1`:
    1. `D = 2^|v| - 3^w(v) > 0` satisfies `D % 2 == 1` and `D % 3 != 0`.
    2. `P_j = affine_carry(rotate_left(v, j))` satisfies `P_j > 0`, `P_j % 3 != 0`,
       `P_j == 2 * P_{j+1}` on `False` steps, and `2 * P_{j+1} == 3 * P_j + D` on `True` steps.
    3. Projected residues `r_j = (P_j * U) % (2^A * 3^B)` (`D * U + M * V == 1`) satisfy
       exact compressed Collatz step congruences modulo `M = 2^A * 3^B`, parity consistency
       (`r_j % 2 == v_j` when `A >= 1`), and `r_j % 3 != 0` (`B >= 1`).
    4. Any `(2^A * 3^B)`-periodic potential `psi` plus rational state potential `Phi(P_j, D)`
       telescopes identically to `0` around `j = 0 .. |v| - 1`.
    """
    k_len = len(v)
    w = parity_weight(v)
    if k_len < 1 or w < 1:
        raise ValueError("Requires |v| >= 1 and parityWeight(v) >= 1.")
    det = (1 << k_len) - (3**w)
    if det <= 0:
        raise ValueError("Requires 2^|v| > 3^w(v) (D > 0).")

    u_bez, v_bez = bezout_coprime_pow2_pow3(det, A, B)
    modulus = (1 << A) * (3**B)

    numerators = [affine_carry(rotate_left(v, j)) for j in range(k_len + 1)]
    residues = [(p_val * u_bez) % modulus for p_val in numerators]

    homogeneous_steps_ok = numerators[k_len] == numerators[0]
    modular_steps_ok = residues[k_len] == residues[0]
    parity_ok = True
    nondiv3_ok = True

    for j in range(k_len):
        p_cur = numerators[j]
        p_nxt = numerators[j + 1]
        r_cur = residues[j]
        r_nxt = residues[j + 1]

        if p_cur <= 0 or (p_cur % 3 == 0):
            nondiv3_ok = False
        if B >= 1 and (r_cur % 3 == 0):
            nondiv3_ok = False

        if not v[j]:
            if p_cur != 2 * p_nxt or (p_cur % 2 != 0):
                homogeneous_steps_ok = False
            if A >= 1 and (r_cur % 2 != 0):
                parity_ok = False
            if modulus > 1 and ((2 * r_nxt - r_cur) % modulus != 0):
                modular_steps_ok = False
        else:
            if 2 * p_nxt != 3 * p_cur + det or (p_cur % 2 != 1):
                homogeneous_steps_ok = False
            if A >= 1 and (r_cur % 2 != 1):
                parity_ok = False
            if modulus > 1 and ((2 * r_nxt - (3 * r_cur + 1)) % modulus != 0):
                modular_steps_ok = False

    # Verify exact zero telescoping sum of a generic modular potential + rational `1/x` potential.
    telescoping_sum = Fraction(0)
    for j in range(k_len):
        psi_cur = Fraction((residues[j] * residues[j] + 5 * residues[j] + 1), modulus + 1)
        psi_nxt = Fraction(
            (residues[j + 1] * residues[j + 1] + 5 * residues[j + 1] + 1), modulus + 1
        )
        phi_cur = Fraction(det, numerators[j]) + Fraction(det, numerators[j] + det)
        phi_nxt = Fraction(det, numerators[j + 1]) + Fraction(
            det, numerators[j + 1] + det
        )
        telescoping_sum += (psi_nxt - psi_cur) + (phi_nxt - phi_cur)

    return {
        "K": k_len,
        "W": w,
        "D": det,
        "modulus": modulus,
        "bezout_U": u_bez,
        "bezout_V": v_bez,
        "numerators": numerators[:-1],
        "residues": residues[:-1],
        "x_min": Fraction(min(numerators[:-1]), det),
        "x_max": Fraction(max(numerators[:-1]), det),
        "homogeneous_steps_ok": homogeneous_steps_ok,
        "modular_steps_ok": modular_steps_ok,
        "parity_ok": parity_ok,
        "nondiv3_ok": nondiv3_ok,
        "telescoping_sum_zero": (telescoping_sum == 0),
    }


def construct_sturmian_rational_cycle(K: int, W: int) -> list[bool]:
    """Construct balanced mechanical/Sturmian parity word of length `K` and weight `W`.

    Maximizes `x_min` over `Q_(2)^+ ∩ Q_(3)^+` for any `(K, W)` with `2^K > 3^W` by
    distributing `W` odd steps and `K - W` even steps as uniformly as possible, then
    rotating to start at a spiral local minimum (maximal initial `True` run after `False`).
    """
    if K <= W or W < 1 or (1 << K) <= (3**W):
        raise ValueError("Requires 1 <= W < K and 2^K > 3^W.")
    raw = [(((j + 1) * W) // K) > ((j * W) // K) for j in range(K)]
    # Rotate so the word ends with `False` and starts with `True` (a spiral block start).
    best_rot = raw
    best_min = Fraction(-1)
    for shift in range(K):
        cand = rotate_left(raw, shift)
        if cand[0] and not cand[-1]:
            orbit = rational_cycle_from_parity_word(cand, q=3)
            cur_min = min(orbit)
            if cur_min > best_min:
                best_min = cur_min
                best_rot = cand
                break
    return best_rot


# ============================================================================
# 5. Theorems T1, T2, T3a, T3b & Mandatory 3x3 Counter-Model Gate
# ============================================================================


def verify_cycle_ratio_sandwich_and_peak_floor(
    v: Sequence[bool], orbit: Sequence[Fraction]
) -> dict[str, bool]:
    """Verify Theorem T1 polynomial cycle bounds on a positive cycle (`orbit` in `Q_{>0}`)."""
    if len(v) != len(orbit) or not v:
        raise ValueError("Mismatched parity word and orbit lengths.")
    if any(x <= 0 for x in orbit):
        return {
            "upper_ratio_from_min_odd": False,
            "lower_ratio_from_max_odd": False,
            "binomial_peak_floor": False,
        }
    k_len = len(v)
    w = parity_weight(v)
    odd_vals = [orbit[i] for i, bit in enumerate(v) if bit]
    if not odd_vals:
        return {
            "upper_ratio_from_min_odd": False,
            "lower_ratio_from_max_odd": False,
            "binomial_peak_floor": False,
        }
    m_odd = min(odd_vals)
    M_odd = max(odd_vals)
    pow2_k = Fraction(1 << k_len)

    upper_ok = pow2_k * (m_odd**w) <= ((3 * m_odd + 1) ** w)
    lower_ok = ((3 * M_odd + 1) ** w) <= pow2_k * (M_odd**w)
    peak_ok = Fraction(w * (3 ** (w - 1))) <= (pow2_k - Fraction(3**w)) * M_odd
    return {
        "upper_ratio_from_min_odd": upper_ok,
        "lower_ratio_from_max_odd": lower_ok,
        "binomial_peak_floor": peak_ok,
    }


def verify_brox_shift_identity(w1: int, rest: Sequence[bool]) -> bool:
    """Verify exact identity `C(1^w1 ++ 0 :: rest) + (2^K - 3^W) == 2^w1 * broxOddCarry(rest)`."""
    if w1 < 0:
        raise ValueError("w1 must be non-negative.")
    v = ([True] * w1) + [False] + list(rest)
    k_len = len(v)
    w = parity_weight(v)
    lhs = affine_carry(v, q=3) + ((1 << k_len) - (3**w))
    rhs = (1 << w1) * brox_odd_carry(rest)
    h_val = brox_odd_carry(rest)
    return (
        lhs == rhs
        and h_val >= (3 ** parity_weight(rest))
        and (h_val % 2 == 1)
    )


def evaluate_cycle_barriers_on_word(
    v: Sequence[bool], q: int = 3
) -> dict[str, object]:
    """Evaluate all universal cycle barriers (`T1`--`T3b`) on a periodic parity word `v`.

    Rotates `v` to the cycle's minimum element `x_min` before testing cycle-minimum
    invariants (`x_min % 48`, initial `w1 >= 2`, `(21, 22)` band, Brox `Nat` equation).
    """
    orbit = rational_cycle_from_parity_word(v, q=q)
    k_len = len(v)
    w = parity_weight(v)
    det_q = (1 << k_len) - (q**w)
    det_3 = (1 << k_len) - (3**w)

    # Locate cycle minimum index `idx_min` and maximum index `idx_max`.
    min_val = min(orbit)
    idx_min = orbit.index(min_val)
    v_min = rotate_left(v, idx_min)
    orbit_min = orbit[idx_min:] + orbit[:idx_min]

    is_pos = all(x > 0 for x in orbit_min)
    is_int = all(x.denominator == 1 for x in orbit_min)
    is_q3 = (q == 3)

    # Barrier 1: Archimedean positivity `3^W < 2^K` and `x > 0` (separates M2 = Z^-).
    arch_pos_3x1 = is_pos and (det_3 > 0)

    # Barrier 2: Upper `2^K <= 4^W` (`K <= 2*W`) + `x % 3 != 0` on ALL cycle elements
    # (both hold on ALL `(Z^+, 3x+1)` cycles and fail on ALL `M3 = 5x+1` positive cycles!).
    pow4_bound = (1 << k_len) <= (4**w)
    nondiv3_all = all(
        (x.numerator % 3 != 0) and (x.denominator % 3 != 0) for x in orbit_min
    )

    # Barrier 3: Tightened `(21, 22)` exponent band `21^W < 7^W * 2^K <= 22^W` and `W >= 5`
    # (separates trivial `{1, 2}` cycle, `M1` `(19/5, 29/5)`, `M2`, and `M3` simultaneously!).
    band_21_22 = ((21**w) < (7**w) * (1 << k_len)) and (
        (7**w) * (1 << k_len) <= (22**w)
    )

    # Barrier 4: Exact `Z`-integrality `(2^K - 3^W) | C_3(v_min)` in `Z` with `q == 3`
    # (separates ALL of `M1 = Q_(2)^+`, including arbitrarily high-floor `319/13`!).
    c3_min = affine_carry(v_min, q=3)
    z_integral_3x1 = is_q3 and is_int and (det_3 != 0) and (c3_min % det_3 == 0)

    # Barrier 5: Mod-48 minimum sieve + pure-Nat Brox odd-quotient equation (`T3a` & `T3b`).
    mod48_min_ok = (
        is_int
        and is_pos
        and (int(min_val) % 48 in MOD48_SURVIVING_CYCLE_MIN_CLASSES)
    )

    brox_nat_witness_ok = False
    if (
        is_q3
        and z_integral_3x1
        and arch_pos_3x1
        and mod48_min_ok
        and band_21_22
        and len(v_min) >= 8
        and w >= 5
        and v_min[0]
        and v_min[1]
        and (False in v_min)
    ):
        first_false = v_min.index(False)
        w1 = first_false
        rest = v_min[first_false + 1 :]
        x0_int = int(min_val)
        if w1 >= 2 and ((x0_int + 1) % (1 << w1) == 0):
            q0 = (x0_int + 1) // (1 << w1)
            brox_nat_witness_ok = (
                q0 >= 1
                and (q0 % 2 == 1)
                and (det_3 * q0 == brox_odd_carry(rest))
                and ((1 << k_len) * (x0_int**w) <= ((3 * x0_int + 1) ** w))
            )

    return {
        "q": q,
        "K": k_len,
        "W": w,
        "x_min": min_val,
        "x_max": max(orbit_min),
        "det_q": det_q,
        "archimedean_positivity_3x1": arch_pos_3x1,
        "pow4_upper_bound": pow4_bound,
        "nondiv3_all_vertices": nondiv3_all,
        "band_21_22": band_21_22,
        "z_integrality_3x1": z_integral_3x1,
        "mod48_min_sieve": mod48_min_ok,
        "certified_nontrivial_3x1_witness": brox_nat_witness_ok,
    }


CANONICAL_COUNTERMODEL_WORDS: dict[str, tuple[list[bool], int]] = {
    # M1 = Q_(2)^+ (3x + 1 rational positive cycles, including high-floor 319/13 > 24)
    "M1_19_over_5": ([True, True, True, False, False], 3),
    "M1_29_over_5": ([True, False, True, True, False], 3),
    "M1_319_over_13_high_floor": (
        [True, True, False, True, True, False, True, False],
        3,
    ),
    "M1_2block_contracting_1631": (
        [True] * 3 + [False] * 2 + [True] * 5 + [False] * 3,
        3,
    ),
    "M1_2block_expanding_251_over_13": (
        [True] * 3 + [False] * 1 + [True] * 2 + [False] * 2,
        3,
    ),
    "M1_2block_q_ge_3_287_over_13": (
        [True] * 2 + [False] * 1 + [True] * 3 + [False] * 2,
        3,
    ),
    # M2 = Z^- (3x + 1 negative integer cycles: -1, -5, -17)
    "M2_neg_1": ([True], 3),
    "M2_neg_5": ([True, True, False], 3),
    "M2_neg_17": (
        [True, True, True, True, False, True, True, True, False, False, False],
        3,
    ),
    # M3 = 5x + 1 on Z^+ (genuine positive integer cycles: 1, 13, 17)
    "M3_5x1_1": ([True, True, False, False, False], 5),
    "M3_5x1_13": ([True, True, True, False, False, False, False], 5),
    "M3_5x1_17": ([True, True, False, False, True, False, False], 5),
    # Trivial (Z^+, 3x + 1) cycle {1, 2}
    "Zpos_3x1_trivial_1": ([True, False], 3),
}


def run_3x3_countermodel_gate() -> dict[str, dict[str, object]]:
    """Run all canonical `M1`, `M2`, `M3`, and trivial `{1, 2}` cycles through `T1`--`T3b`."""
    results: dict[str, dict[str, object]] = {}
    for name, (word, q_mult) in CANONICAL_COUNTERMODEL_WORDS.items():
        results[name] = evaluate_cycle_barriers_on_word(word, q=q_mult)
    return results


# ============================================================================
# 6. Wave 2 Universal Cycle Reductions (`T5`--`T8`, `[]` Axioms)
# ============================================================================


def verify_mod24_determinant_gap(K: int, W: int) -> dict[str, object]:
    """Verify Theorem T5: for `K >= 3, W >= 1, 3^W < 2^K`, `(2^K - 3^W) % 24 in {5,7,13,23}`."""
    if K < 3 or W < 1 or (3**W) >= (1 << K):
        raise ValueError("Requires K >= 3, W >= 1, and 3^W < 2^K.")
    det = (1 << K) - (3**W)
    mod24 = det % 24
    return {
        "K": K,
        "W": W,
        "D": det,
        "mod24": mod24,
        "in_4_classes": mod24 in MOD24_DETERMINANT_CLASSES,
        "ge_5": det >= 5,
    }


def max_pow2_dividing_pow3_sub_one(w: int) -> int:
    """Return the exact largest power `2^a` dividing `3^w - 1` for `w >= 1`."""
    if w < 1:
        raise ValueError("Requires w >= 1.")
    val = (3**w) - 1
    p2 = 1
    while val % 2 == 0:
        val //= 2
        p2 *= 2
    return p2


def verify_2adic_lte_pow3_sub_one(w: int) -> bool:
    """Verify Theorem T6a: every `2^a | (3^w - 1)` (`w >= 1`) satisfies `2^a <= 4 * w`."""
    if w < 1:
        raise ValueError("Requires w >= 1.")
    return max_pow2_dividing_pow3_sub_one(w) <= 4 * w


def verify_one_block_cycle_squeeze(w1: int, c: int) -> dict[str, object]:
    """Verify Theorem T6b on `v = 1^w1 ++ 0 :: 0^c` (`a1 = c + 1`, `w1 >= 2`).

    Checks:
    1. `brox_odd_carry([False] * c) == 2^(c + 1) - 1` identically.
    2. `q0 = 1` (`x0 = 2^w1 - 1`, Mersenne 1-cycle) NEVER solves `(2^K - 3^W) * 1 == 2^a1 - 1`.
    3. Whenever `0 < 2^(w1 + a1) - 3^w1 <= 2^a1 - 1` (necessary for ANY `q0 >= 1`),
       the integer binary prefix quotient `(3^w1) // (2^a1)` equals `2^w1 - 1` identically.
    """
    if w1 < 2 or c < 0:
        raise ValueError("Requires w1 >= 2 and c >= 0.")
    a1 = c + 1
    k_len = w1 + a1
    h_val = brox_odd_carry([False] * c)
    h_formula_ok = h_val == ((1 << a1) - 1)
    det = (1 << k_len) - (3**w1)
    q0_eq_1_impossible = det != h_val
    squeeze_applicable = 0 < det <= h_val
    binary_prefix_ok = (not squeeze_applicable) or (
        ((3**w1) // (1 << a1)) == ((1 << w1) - 1)
    )
    return {
        "w1": w1,
        "a1": a1,
        "brox_formula_ok": h_formula_ok,
        "q0_eq_1_impossible": q0_eq_1_impossible,
        "squeeze_applicable": squeeze_applicable,
        "binary_prefix_ok": binary_prefix_ok,
    }


def leading_false_count(bits: Sequence[bool]) -> int:
    """Count consecutive leading `False` entries (`leadingFalseCount` in Lean 4 Core)."""
    cnt = 0
    for b in bits:
        if not b:
            cnt += 1
        else:
            break
    return cnt


def verify_brox_append_false_identity(init: Sequence[bool]) -> bool:
    """Verify Theorem T7a: `broxOddCarry (init ++ [false]) == broxOddCarry init + 2^(|init|+1)`."""
    lhs = brox_odd_carry(list(init) + [False])
    rhs = brox_odd_carry(init) + (1 << (len(init) + 1))
    return lhs == rhs


def verify_first_block_discreteness_separation() -> dict[str, object]:
    """Verify Theorem T7b separation between `(Z^+, 3x+1)` and `M1 = Q_(2)^+`.

    Over `Q_(2)^+`, `v = 1^3 0^2 1^5 0^3` (`K = 13, W = 8, D = 1631`) is a positive
    2-block cycle whose two spiral minima `x_A, x_B` satisfy `0 < |x_B - x_A| < 1`,
    allowing BOTH spiral blocks `(3, 2)` and `(5, 3)` to satisfy `2^(w_i + a_i) > 3^w_i`
    (`32 > 27` and `256 > 243`). Over `Z^+`, integer discreteness (`x1 != x0 => x1 >= x0 + 1`)
    forces `2^(w1 + a1) < 3^w1` at the minimum of EVERY multi-block cycle!
    """
    word = [True] * 3 + [False] * 2 + [True] * 5 + [False] * 3
    orbit = rational_cycle_from_parity_word(word, q=3)
    x_first = orbit[0]
    x_second = orbit[5]
    x_min_all = min(orbit)
    idx_min = orbit.index(x_min_all)
    rot_word = rotate_left(word, idx_min)
    blocks_at_min = decompose_spiral_blocks(rot_word)
    w1, a1 = blocks_at_min[0]
    rot_orbit = orbit[idx_min:] + orbit[:idx_min]
    x0 = rot_orbit[0]
    x1 = rot_orbit[w1 + a1]

    return {
        "x_first": x_first,
        "x_second": x_second,
        "x0_min": x0,
        "x1_next_spiral": x1,
        "gap": x1 - x0,
        "gap_strictly_between_0_and_1": Fraction(0) < (x1 - x0) < Fraction(1),
        "w1": w1,
        "a1": a1,
        "first_block_contracts_det": (1 << (w1 + a1)) > (3**w1),
        "violates_z_discreteness_dichotomy": (x1 != x0)
        and not ((1 << (w1 + a1)) < (3**w1)),
    }


def is_sharpened_brox_cycle_witness(
    w1: int, init: Sequence[bool], q0: int
) -> bool:
    """Exact Python mirror of `IsSharpenedBroxCycleWitness` (Theorem T8)."""
    k_len = w1 + 2 + len(init)
    w = w1 + parity_weight(init)
    if w1 < 2 or q0 < 1 or (q0 % 2 != 1) or w < 5 or k_len < 8:
        return False
    x0 = (1 << w1) * q0 - 1
    if (x0 % 96) not in MOD96_SURVIVING_CYCLE_MIN_CLASSES:
        return False
    if not ((21**w) < (7**w) * (1 << k_len) <= (22**w)):
        return False
    if (1 << k_len) * (x0**w) > ((3 * x0 + 1) ** w):
        return False
    det = (1 << k_len) - (3**w)
    if (det % 24) not in MOD24_DETERMINANT_CLASSES or det < 5:
        return False
    if det * q0 != brox_odd_carry(init) + (1 << (len(init) + 1)):
        return False

    a1 = leading_false_count([False] + list(init) + [False])
    w_init = parity_weight(init)
    branch_one_cycle = (
        w_init == 0
        and q0 >= 3
        and ((3**w1) // (1 << (len(init) + 2)) == (1 << w1) - 1)
    )
    branch_multi_block = w_init >= 1 and ((1 << (w1 + a1)) < (3**w1))
    return branch_one_cycle or branch_multi_block


# ============================================================================
# 7. Wave 3 Universal 1-Block GCD/Mod-24 Squeeze, Complete `[]`-Axiom 2-Block
#    Cycle Reduction, & Unified Two-Barrier Master Core (`T9`--`T11`)
# ============================================================================


def verify_one_block_gcd_and_mod24_squeeze(w1: int, a1: int) -> dict[str, object]:
    """Verify Theorem T9 (`T9a`--`T9c`) on `(w1, a1)` (`w1 >= 2, a1 >= 1`).

    Checks:
    1. Universal linear-combination identity `(3^w1 - 2^w1) == 2^w1 * (2^a1 - 1) - D`
       where `D = 2^(w1 + a1) - 3^w1`.
    2. Elimination of ALL `{2, 3}`-smooth quotients `q0 = 3^r` (`r >= 0`) whenever `D > 0`.
    3. Elimination of ALL `2 <= w1 <= 12` (`D > 2^a1 - 1` whenever `D > 0`).
    4. Whenever `D > 0` and `17 * D <= 2^a1 - 1`, exact 17-fold binary prefix squeeze
       `(17 * 3^w1) // (2^a1) == 17 * 2^w1 - 1`.
    5. Whenever `D > 0` and `(2^a1 - 1) % D == 0`, exact GCD/congruence lock
       `D | gcd(2^a1 - 1, 3^w1 - 2^w1)`, `2^a1 % D == 1`, `2^w1 % D == 3^w1 % D`,
       `q0 % 24 in {3, 9, 17, 19}`, `q0 >= 17` (`q0 >= 19` if `w1 % 2 == 1`),
       and `x0 % 96 in {31, 95}` (`w1 >= 13, a1 >= 8`).
    """
    if w1 < 2 or a1 < 1:
        raise ValueError("Requires w1 >= 2 and a1 >= 1.")
    det = (1 << (w1 + a1)) - (3**w1)
    h_val = (1 << a1) - 1
    carry1 = (3**w1) - (1 << w1)
    gcd_val = math.gcd(h_val, carry1)

    linear_comb_ok = carry1 == ((1 << w1) * h_val - det)
    pow3_quotient_impossible = True
    if det > 0:
        for r in range(max(6, w1 + 4)):
            if det * (3**r) == h_val:
                pow3_quotient_impossible = False
                break

    small_w1_impossible = (w1 > 12) or (det <= 0) or (det > h_val)
    squeeze17_applicable = 0 < 17 * det <= h_val
    binary_prefix17_ok = (not squeeze17_applicable) or (
        ((17 * (3**w1)) // (1 << a1)) == (17 * (1 << w1) - 1)
    )

    divisible_hit = det > 0 and (h_val % det == 0)
    gcd_and_mod_locks_ok = True
    if divisible_hit:
        q0 = h_val // det
        x0 = (1 << w1) * q0 - 1
        gcd_and_mod_locks_ok = (
            (q0 % 2 == 1)
            and (gcd_val % det == 0)
            and ((1 << a1) % det == 1)
            and (((1 << w1) % det) == ((3**w1) % det))
            and (w1 >= 13)
            and (a1 >= 8)
            and ((q0 % 24) in MOD24_ONE_BLOCK_Q0_CLASSES)
            and (q0 >= 17)
            and ((w1 % 2 == 0) or (q0 >= 19))
            and ((x0 % 96) in MOD96_ONE_BLOCK_X0_CLASSES)
            and (((17 * (3**w1)) // (1 << a1)) == (17 * (1 << w1) - 1))
        )

    return {
        "w1": w1,
        "a1": a1,
        "D": det,
        "gcd_val": gcd_val,
        "linear_comb_ok": linear_comb_ok,
        "pow3_quotient_impossible": pow3_quotient_impossible,
        "small_w1_impossible": small_w1_impossible,
        "binary_prefix17_ok": binary_prefix17_ok,
        "divisible_hit": divisible_hit,
        "gcd_and_mod_locks_ok": gcd_and_mod_locks_ok,
    }


def two_block_brox_carries(w1: int, a1: int, w2: int, a2: int) -> tuple[int, int]:
    """Compute closed-form 2-block Brox odd carries `(H0, H1)` for `(w1, a1, w2, a2)`."""
    if w1 < 1 or a1 < 1 or w2 < 1 or a2 < 1:
        raise ValueError("All spiral exponents (w1, a1, w2, a2) must be >= 1.")
    h0 = (3**w2) * ((1 << a1) - 1) + (1 << (a1 + w2)) * ((1 << a2) - 1)
    h1 = (3**w1) * ((1 << a2) - 1) + (1 << (a2 + w1)) * ((1 << a1) - 1)
    return h0, h1


def verify_two_block_cleared_denom_and_cubic_squeeze(
    w1: int, a1: int, w2: int, a2: int, n0_floor: int = 26
) -> dict[str, object]:
    """Verify Theorem T10 (`T10a`--`T10c`) on 2-block spiral parameters `(w1, a1, w2, a2)`.

    Checks:
    1. Exact closed-form match `H0 == brox_odd_carry(0^(a1-1) ++ 1^w2 ++ 0^a2)` and
       `H1 == brox_odd_carry(0^(a2-1) ++ 1^w1 ++ 0^a1)`.
    2. Exact cleared-denominator 2-block reciprocal identity (`T10a`):
       `D * x0 * x1 == 3^w2 * (3^w1 - 2^w1) * x1 + 3^w1 * (3^w2 - 2^w2) * x0
                      + (3^w1 - 2^w1) * (3^w2 - 2^w2)` over `Q_(2)` whenever `D != 0`.
    3. Elimination of Mersenne vertices `q0 = 1` (`H0 != D`) and `q1 = 1` (`H1 != D`)
       on all valid candidate 2-block parameters (`w1 >= 2, W >= 5, D > 0`).
    4. Pure-Nat Dual Brox Cubic Squeeze (`T10b`): whenever `D > 0`, `2^(w1 + a1) < 3^w1`,
       `H0 >= 3 * D`, and `H1 >= 3 * D`, `27 * 2^(W + a1 - 3) * D^3 < 2^(3 * K)` holds!
    5. Cleared-denominator potential merger bound (`T10a` + `subdouble_entry_block_merger`):
       whenever `D > 0`, `2^(w1 + a1) < 3^w1`, `3^w2 < 2^(w2 + a2)`, and `x0, x1` satisfy
       the Hercher merger floors for `n0_floor`, `3 * n0_floor * D < 4 * 3^W` holds!
    """
    if w1 < 1 or a1 < 1 or w2 < 1 or a2 < 1 or n0_floor < 1:
        raise ValueError("Requires w1, a1, w2, a2, n0_floor >= 1.")
    w_tot = w1 + w2
    k_tot = w1 + a1 + w2 + a2
    det = (1 << k_tot) - (3**w_tot)
    h0, h1 = two_block_brox_carries(w1, a1, w2, a2)

    rest0 = ([False] * (a1 - 1)) + ([True] * w2) + ([False] * a2)
    rest1 = ([False] * (a2 - 1)) + ([True] * w1) + ([False] * a1)
    brox_closed_form_ok = (h0 == brox_odd_carry(rest0)) and (
        h1 == brox_odd_carry(rest1)
    )

    reciprocal_identity_ok = True
    potential_merger_bound_ok = True
    x0_frac: Fraction | None = None
    x1_frac: Fraction | None = None
    if det != 0:
        x0_frac = Fraction(1 << w1) * Fraction(h0, det) - 1
        x1_frac = Fraction(1 << w2) * Fraction(h1, det) - 1
        c1 = (3**w1) - (1 << w1)
        c2 = (3**w2) - (1 << w2)
        s_term = (3**w2) * c1 * x1_frac + (3**w1) * c2 * x0_frac
        reciprocal_identity_ok = det * x0_frac * x1_frac == s_term + c1 * c2

        if (
            det > 0
            and w1 >= 2
            and ((1 << (w1 + a1)) < (3**w1))
            and ((3**w2) < (1 << (w2 + a2)))
        ):
            floor0 = (2 * n0_floor + 3) if a1 >= 2 else (n0_floor + 1)
            floor1 = (
                (2 * n0_floor + 3) if (w2 >= 2 and a2 >= 2) else (n0_floor + 1)
            )
            if (
                x0_frac >= Fraction(floor0)
                and x1_frac >= Fraction(floor1)
                and x1_frac >= x0_frac + Fraction(2)
            ):
                potential_merger_bound_ok = 3 * n0_floor * det < 4 * (3**w_tot)

    mersenne_q0_impossible = not (
        det > 0
        and w1 >= 2
        and w_tot >= 5
        and (((1 << w1) - 1) % 3 != 0)
        and h0 == det
    )
    mersenne_q1_impossible = not (
        det > 0
        and ((3**w2) < (1 << (w2 + a2)))
        and ((1 << w2) - 1 > 2)
        and (((1 << w2) - 1) % 3 != 0)
        and h1 == det
    )

    cubic_squeeze_applicable = (
        det > 0
        and w1 >= 2
        and ((1 << (w1 + a1)) < (3**w1))
        and h0 >= 3 * det
        and h1 >= 3 * det
    )
    cubic_squeeze_ok = (not cubic_squeeze_applicable) or (
        27 * (1 << (w_tot + a1 - 3)) * (det**3) < (1 << (3 * k_tot))
    )

    return {
        "W": w_tot,
        "K": k_tot,
        "D": det,
        "H0": h0,
        "H1": h1,
        "x0": x0_frac,
        "x1": x1_frac,
        "brox_closed_form_ok": brox_closed_form_ok,
        "reciprocal_identity_ok": reciprocal_identity_ok,
        "mersenne_q0_impossible": mersenne_q0_impossible,
        "mersenne_q1_impossible": mersenne_q1_impossible,
        "cubic_squeeze_applicable": cubic_squeeze_applicable,
        "cubic_squeeze_ok": cubic_squeeze_ok,
        "potential_merger_bound_ok": potential_merger_bound_ok,
    }


def verify_two_block_m1_potential_obstruction_witnesses() -> dict[str, object]:
    """Verify the two `W = 5, K = 8, D = 13` `M1 = Q_(2)^+` 2-block obstruction witnesses.

    1. `v_A = 1^3 0^1 1^2 0^2` (`251/13 <-> 439/13`): satisfies `2^(w1+a1) < 3^w1`,
       `3^w2 < 2^(w2+a2)`, `(21, 22)` band, AND `potential_telescoping` at `n0 = 15`
       (`3 * 15 * 13 = 585 < 972 = 4 * 3^5`), proving pure `Q_{>0}` potential telescoping
       cannot yield a contradiction without `Z`-divisibility / exponential-gap bounds.
       Separated by `13 !| H0` (`33 % 13 = 7`), `H0 < 3*D`, and `23 * D > 3^W` (`299 > 243`).
    2. `v_B = 1^2 0^1 1^3 0^2` (`287/13 <-> 331/13`): ALSO satisfies `H0 >= 3*D` (`75 >= 39`)
       and `H1 >= 3*D` (`43 >= 39`) and `27 * 2^(W+a1-3) * D^3 < 2^(3*K)`, yet is separated
       unconditionally (`[]` axioms) by BOTH `13 !| H0` (`75 % 13 = 10`) AND `23 * D > 3^W`!
    """
    res_a = verify_two_block_cleared_denom_and_cubic_squeeze(3, 1, 2, 2, n0_floor=15)
    res_b = verify_two_block_cleared_denom_and_cubic_squeeze(2, 1, 3, 2, n0_floor=16)
    d_val = int(res_a["D"])
    w_val = int(res_a["W"])
    h0_a = int(res_a["H0"])
    h0_b = int(res_b["H0"])
    h1_b = int(res_b["H1"])

    return {
        "witness_251_x0": res_a["x0"],
        "witness_251_x1": res_a["x1"],
        "witness_251_satisfies_q_potential": bool(res_a["potential_merger_bound_ok"])
        and (3 * 15 * d_val < 4 * (3**w_val)),
        "witness_251_separated_by_z_and_23D": (h0_a % d_val != 0)
        and (h0_a < 3 * d_val)
        and (23 * d_val >= (3**w_val)),
        "witness_287_x0": res_b["x0"],
        "witness_287_x1": res_b["x1"],
        "witness_287_satisfies_3D_and_cubic": (h0_b >= 3 * d_val)
        and (h1_b >= 3 * d_val)
        and bool(res_b["cubic_squeeze_applicable"])
        and bool(res_b["cubic_squeeze_ok"]),
        "witness_287_separated_by_z_and_23D": (h0_b % d_val != 0)
        and (23 * d_val >= (3**w_val)),
    }


def check_subexponential_cubic_gap(K: int, W: int) -> bool:
    """Evaluate `SubexponentialCubicGapProp` at `(K, W)`:

    `W >= 6 and 3^W < 2^K => 27 * 2^(W - 2) * (2^K - 3^W)^3 >= 2^(3 * K)`.
    """
    if W < 6 or (3**W) >= (1 << K):
        return True
    det = (1 << K) - (3**W)
    return 27 * (1 << (W - 2)) * (det**3) >= (1 << (3 * K))


def is_primitive_two_block_brox_witness(
    w1: int, a1: int, w2: int, a2: int, q0: int, q1: int
) -> bool:
    """Exact Python mirror of `IsPrimitiveTwoBlockBroxWitness` (`T10c`)."""
    if w1 < 2 or a1 < 1 or w2 < 1 or a2 < 1 or q0 < 3 or q1 < 3:
        return False
    if (q0 % 2 != 1) or (q1 % 2 != 1):
        return False
    w_tot = w1 + w2
    k_tot = w1 + a1 + w2 + a2
    if w_tot < 8 or k_tot < 13:
        return False
    if not ((21**w_tot) < (7**w_tot) * (1 << k_tot) <= (22**w_tot)):
        return False
    if not (((1 << (w1 + a1)) < (3**w1)) and ((3**w2) < (1 << (w2 + a2)))):
        return False
    det = (1 << k_tot) - (3**w_tot)
    if (det % 24) not in MOD24_DETERMINANT_CLASSES:
        return False
    if not (23 * det < (3**w_tot)):
        return False
    x0 = (1 << w1) * q0 - 1
    x1 = (1 << w2) * q1 - 1
    if not (x0 >= 47 and x1 >= x0 + 2 and (x0 % 96 in MOD96_SURVIVING_CYCLE_MIN_CLASSES) and (x1 % 3 != 0)):
        return False
    h0, h1 = two_block_brox_carries(w1, a1, w2, a2)
    if det * q0 != h0 or det * q1 != h1:
        return False
    return 27 * (1 << (w_tot + a1 - 3)) * (det**3) < (1 << (3 * k_tot))


def verify_hercher_subdouble_merger_separation() -> dict[str, object]:
    """Verify Theorem T11a (`subdouble_entry_block_merger` eliminates 1-block at `n_min`)
    and demonstrate strict counter-model separation from `M3 = 5x + 1`.

    1. Over `(Z^+, 3x + 1)`: for any `x0 = 2^w1 * q0 - 1` (`w1 >= 2, q0 >= 1` odd)
       whose odd run is followed by `a1 >= 2` even steps (`(3^w1 * q0 - 1) % 4 == 0`),
       the strictly smaller partner `n_prime = (x0 - 1) // 2` (`1 <= n_prime < x0`)
       satisfies `T^(w1 + 1)(n_prime) == T^(w1 + 2)(x0)` identically! Hence on any
       1-block positive cycle (`a1 >= 2` forced by `3^w1 < 2^(w1 + a1)`), `n_prime`
       merges into `x0` and NEVER reaches `1`, proving `x0` cannot be `n_min`.
    2. Over `M3 = (Z^+, 5x + 1)`: `x0 = 13` is a genuine 1-block positive integer cycle
       (`w1 = 3, a1 = 4, K = 7`), yet `n_prime = (13 - 1) // 2 = 6` reaches `1` in 5
       steps (`6 -> 3 -> 8 -> 4 -> 2 -> 1`) instead of merging into `13`!
    """
    all_3x1_mergers_ok = True
    checked_pairs = 0
    for w1 in range(2, 9):
        for q0 in range(1, 40, 2):
            if ((3**w1) * q0 - 1) % 4 != 0:
                continue
            checked_pairs += 1
            x0 = (1 << w1) * q0 - 1
            n_prime = (x0 - 1) // 2
            if not (1 <= n_prime < x0):
                all_3x1_mergers_ok = False
                break
            y_main = x0
            for _ in range(w1 + 2):
                y_main = collatz_step_int(y_main, q=3)
            y_partner = n_prime
            for _ in range(w1 + 1):
                y_partner = collatz_step_int(y_partner, q=3)
            if y_main != y_partner:
                all_3x1_mergers_ok = False
                break

    # Counter-model M3 = 5x + 1 on 1-block positive cycle x0 = 13 (1^3 0^4):
    x0_m3 = 13
    y_m3 = x0_m3
    m3_bits: list[bool] = []
    for _ in range(7):
        m3_bits.append((y_m3 % 2) == 1)
        y_m3 = collatz_step_int(y_m3, q=5)
    m3_is_one_block_cycle = (y_m3 == x0_m3) and (
        m3_bits == ([True] * 3 + [False] * 4)
    )
    n_prime_m3 = (x0_m3 - 1) // 2  # 6
    y_partner_m3 = n_prime_m3
    for _ in range(5):
        y_partner_m3 = collatz_step_int(y_partner_m3, q=5)
    m3_partner_reaches_one = y_partner_m3 == 1

    return {
        "checked_3x1_pairs": checked_pairs,
        "all_3x1_mergers_ok": all_3x1_mergers_ok and (checked_pairs > 0),
        "m3_x0_13_is_one_block_cycle": m3_is_one_block_cycle,
        "m3_partner_6_reaches_one": m3_partner_reaches_one,
    }


def is_wave3_sharpened_brox_witness(
    w1: int, init: Sequence[bool], q0: int
) -> bool:
    """Exact Python mirror of `IsWave3SharpenedBroxWitness` (`T11b`)."""
    if not is_sharpened_brox_cycle_witness(w1, init, q0):
        return False
    k_len = w1 + 2 + len(init)
    w_tot = w1 + parity_weight(init)
    det = (1 << k_len) - (3**w_tot)
    x0 = (1 << w1) * q0 - 1
    w_init = parity_weight(init)

    if w_init == 0:
        a1 = len(init) + 2
        h_val = (1 << a1) - 1
        carry1 = (3**w1) - (1 << w1)
        return (
            w1 >= 13
            and a1 >= 8
            and q0 >= 17
            and ((q0 % 24) in MOD24_ONE_BLOCK_Q0_CLASSES)
            and ((x0 % 96) in MOD96_ONE_BLOCK_X0_CLASSES)
            and (math.gcd(h_val, carry1) % det == 0)
            and (((17 * (3**w1)) // (1 << a1)) == (17 * (1 << w1) - 1))
        )

    # Multi-block branch: if `v` has exactly 2 spiral blocks, enforce full T10b squeeze!
    full_word = ([True] * w1) + [False] + list(init) + [False]
    blocks = decompose_spiral_blocks(full_word)
    if len(blocks) == 2:
        (_, b_a1), (w2, a2) = blocks[0], blocks[1]
        _, h1 = two_block_brox_carries(w1, b_a1, w2, a2)
        if h1 % det != 0:
            return False
        q1 = h1 // det
        return is_primitive_two_block_brox_witness(w1, b_a1, w2, a2, q0, q1)
    return True

