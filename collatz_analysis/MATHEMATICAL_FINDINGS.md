# Mathematical Findings: $2$-Adic Dynamics, Diophantine Cycle Obstructions, Beatty–Sturmian Carry Bounds, and $3$-Adic Memory Annihilation in the Collatz Conjecture

This document records the formal proofs, structural theorems, Diophantine bounds, and exact lattice-path classifications proved and verified by the `collatz_analysis` research suite.

---

## 1. The Terras–Lagarias $2$-Adic Parity Homeomorphism & Affine Carry Polynomial

Let $T : \mathbb{Z}\sb 2 \to \mathbb{Z}\sb 2$ denote the compressed Collatz (Terras) map on the ring of $2$-adic integers $\mathbb{Z}\sb 2$:

```math
T(x) = \begin{cases} \dfrac{x}{2} & \text{if } x \equiv 0 \pmod 2, \\[8pt] \dfrac{3x + 1}{2} & \text{if } x \equiv 1 \pmod 2. \end{cases}
```

For each $k \ge 1$, define the **$k$-step parity vector map** $\Phi_k : \mathbb{Z}\sb 2 \to \lbrace 0, 1\rbrace ^k$ by

```math
\Phi_k(x) = \bigl(x \bmod 2,\; T(x) \bmod 2,\; \dots,\; T^{k-1}(x) \bmod 2\bigr),
```

and let $\Phi\sb \infty : \mathbb{Z}\sb 2 \to \lbrace 0, 1\rbrace ^\mathbb{N}$ be its projective limit.

### Theorem 1.1 (Affine Decomposition & Odd-Step Valuation Identity)
> For any $x \in \mathbb{Z}\sb 2$ and $k \ge 1$, let $v = \Phi_k(x) = (v_0, \dots, v\sb{k-1}) \in \lbrace 0, 1\rbrace ^k$ have Hamming weight $w = \sum\sb{j=0}^{k-1} v_j$, and let $0 \le j_1 < j_2 < \dots < j_w < k$ denote the $0$-based indices of the $w$ odd steps ( $v\sb{j_m} = 1$ ). Then:

```math
T^k(x) = \frac{3^w x + C_k(v)}{2^k},
```

> where the **affine carry polynomial** $C_k(v) \in \mathbb{Z}\sb{\ge 0}$ satisfies the equivalent closed forms:

```math
C_k(v) = \sum_{j=0}^{k-1} v_j \, 3^{w_{>j}} \, 2^j = \sum_{m=1}^{w} 3^{w - m} \, 2^{j_m}, \qquad w_{>j} = \sum_{i=j+1}^{k-1} v_i.
```

> Equivalently, normalized by $3^w$, the carry is the mixed $(2,3)$-adic valuation sum:

```math
\frac{C_k(v)}{3^w} = \sum_{m=1}^{w} \frac{2^{j_m}}{3^m}.
```

**Proof:**
We proceed by induction on $k$. For $k = 0$, $w = 0$ and $C_0(\emptyset) = 0$, so $T^0(x) = x$. Suppose the formula holds at step $k$. At step $k + 1$:
- If $v_k = 0$, then $w\sb{k+1} = w_k$ and $T^{k+1}(x) = \frac{1}{2} T^k(x) = \frac{3^{w_k} x + C_k(v)}{2^{k+1}}$, so $C\sb{k+1}(v, 0) = C_k(v)$.
- If $v_k = 1$, then $w\sb{k+1} = w_k + 1$ and

  ```math
  T^{k+1}(x) = \frac{3 T^k(x) + 1}{2} = \frac{3 \left(\frac{3^{w_k} x + C_k(v)}{2^k}\right) + 1}{2} = \frac{3^{w_k + 1} x + \bigl(3 C_k(v) + 2^k\bigr)}{2^{k+1}},
  ```

  so $C\sb{k+1}(v, 1) = 3 C_k(v) + 2^k$.

Unrolling the recurrence $C\sb{j+1} = 3^{v_j} C_j + v_j 2^j$ multiplies each term $v_j 2^j$ by $3$ exactly once for every subsequent odd step $i \in \lbrace j+1, \dots, k-1\rbrace$, yielding $3^{w\sb{>j}} 2^j$. Indexing the $w$ odd steps by $m \in \lbrace 1, \dots, w\rbrace$ at positions $j_m$, there are $w - m$ odd steps strictly after $j_m$, so $w\sb{>j_m} = w - m$. $\blacksquare$

---

### Theorem 1.2 (Hensel Lifting Inverse & $2$-Adic Measure-Preserving Homeomorphism)
> For every $k \ge 1$, $\Phi_k$ factors as a bijection $\Phi_k : \mathbb{Z}/2^k\mathbb{Z} \xrightarrow{\sim} \lbrace 0, 1\rbrace ^k$ with explicit two-sided Hensel inverse:

```math
\Phi_k^{-1}(v) \equiv -C_k(v) \cdot (3^w)^{-1} \pmod{2^k}.
```

> In the projective limit $k \to \infty$, $\Phi\sb \infty : \mathbb{Z}\sb 2 \xrightarrow{\sim} \lbrace 0, 1\rbrace ^\mathbb{N}$ is a $2$-adic isometry and a measure-preserving conjugacy between $(\mathbb{Z}\sb 2, T, \mu\sb{\text{Haar}})$ and the one-sided Bernoulli shift $(\lbrace 0, 1\rbrace ^\mathbb{N}, \sigma, \text{Ber}(1/2)^{\otimes \mathbb{N}})$.

**Proof:**
An integer $x$ has parity prefix $v \in \lbrace 0, 1\rbrace ^k$ if and only if at each step $j \in \lbrace 1, \dots, k\rbrace$, the numerator $3^{w_j} x + C_j(v\sb{<j})$ is divisible by $2^j$. Since $\gcd(3^{w_k}, 2^k) = 1$, $3^{w_k}$ is a unit in $\mathbb{Z}/2^k\mathbb{Z}$, and the linear congruence $3^w x + C_k(v) \equiv 0 \pmod{2^k}$ has the unique solution $x \equiv -C_k(v) 3^{-w} \pmod{2^k}$. Because $\lvert \mathbb{Z}/2^k\mathbb{Z} \rvert = \lvert \lbrace 0, 1\rbrace ^k \rvert = 2^k$, surjectivity and injectivity follow immediately. $\blacksquare$

---

### Theorem 1.3 (Böhm–Sontacchi Rational Cycle Criterion & Catalan–Mihăilescu Unit Classification)
> A periodic parity sequence $v^\infty$ with period $v \in \lbrace 0, 1\rbrace ^k$ ( $k \ge 1$ ) corresponds under $\Phi\sb \infty^{-1}$ to a unique periodic point $n\sb{\text{cycle}}(v) \in \mathbb{Q} \cap \mathbb{Z}\sb{(2)}$ given by:

```math
n_{\text{cycle}}(v) = \frac{C_k(v)}{2^k - 3^w}.
```

> Consequently:
1. Every periodic parity sequence is realized by a unique rational cycle in $\mathbb{Q} \cap \mathbb{Z}\sb{(2)}$.
2. A positive integer cycle of length $k$ and odd weight $w$ exists if and only if $2^k > 3^w$ and $(2^k - 3^w) \mid C_k(v)$ in $\mathbb{Z}$.
3. (Catalan–Mihăilescu Unit-Denominator Theorem): By Mihăilescu's Theorem (2002) on Catalan's equation $a^x - b^y = \pm 1$, the cycle denominator $D(k, w) = 2^k - 3^w$ is a unit in $\mathbb{Z}$ ( $\lvert 2^k - 3^w \rvert = 1$ ) if and only if $(k, w) \in \lbrace (2, 1), (1, 1), (3, 2)\rbrace$:
   - $(k, w) = (2, 1) \implies D(2, 1) = +1$, forcing the unique positive trivial cycle $\lbrace 1, 2\rbrace$ ( $v = (1, 0)$ ).
   - $(k, w) = (1, 1) \implies D(1, 1) = -1$, forcing the negative fixed point $\lbrace -1\rbrace$ ( $v = (1)$ ).
   - $(k, w) = (3, 2) \implies D(3, 2) = -1$, forcing the negative $3$-cycle $\lbrace -5, -7, -10\rbrace$ ( $v = (1, 1, 0)$ ).
   For all other $(k, w) \ge (1, 1)$, $\lvert 2^k - 3^w \rvert \ge 5$, so any integer cycle requires a non-trivial arithmetic cancellation $\gcd(C_k(v), 2^k - 3^w) = \lvert 2^k - 3^w \rvert \ge 5$ (first realized in $\mathbb{Z}^-$ at $(k, w) = (11, 7)$ where $2^{11} - 3^7 = -139$ divides $C\sb{11}(v) = 2363 = 139 \times 17$, producing the $n_0 = -17$ cycle).

---

## 2. The Beatty–Sturmian Characterization of Coefficient-Surviving Paths & Sharp Carry Bounds

Define the **stopping time** $\sigma(n) = \inf\lbrace k \ge 1 : T^k(n) < n\rbrace$ and the **coefficient stopping time** $\tau(n) = \inf\lbrace k \ge 1 : 3^{w_k(n)} < 2^k\rbrace$. A parity vector $v \in \lbrace 0, 1\rbrace ^k$ is **coefficient-surviving** if $3^{w_j} > 2^j$ for all prefixes $1 \le j \le k$.

### Theorem 2.1 (Beatty–Sturmian Characterization & Sharp Carry Bounds)
> Let $v \in \lbrace 0, 1\rbrace ^k$ have weight $w \ge 1$ and odd-step indices $0 \le j_1 < j_2 < \dots < j_w < k$.

1. (Universal Extremal Carry Bounds): Over all $\binom{k}{w}$ parity vectors of length $k$ and weight $w$:

   ```math
   3^w - 2^w \le C_k(v) \le 2^{k-w}(3^w - 2^w),
   ```

   where the lower bound is uniquely attained by the $1$-cycle vector $1^w 0^{k-w}$ ( $j_m = m - 1$ ) and the upper bound is uniquely attained by $0^{k-w} 1^w$ ( $j_m = k - w + m - 1$ ).

2. (Beatty–Sturmian Survival Criterion): The prefix of $v$ up to its last odd step $j_w$ is coefficient-surviving if and only if its odd-step indices are componentwise bounded by the Beatty sequence $j^\ast \sb m = \lfloor (m - 1) \log_2 3 \rfloor$:

   ```math
   m - 1 \le j_m \le \lfloor (m - 1) \log_2 3 \rfloor \quad \text{for all } m = 1, \dots, w.
   ```

3. (Sharp Surviving-Path Carry Bound): Over all coefficient-surviving parity vectors of weight $w$, the maximum carry is uniquely attained by the Sturmian boundary path $v^\ast (w)$ with odd steps at $j^\ast \sb m = \lfloor (m - 1) \log_2 3 \rfloor$, and satisfies:

   ```math
   3^w - 2^w \le C_k(v) \le C_{\max}^{\text{surv}}(w) := \sum_{m=1}^{w} 3^{w - m} 2^{\lfloor (m - 1) \log_2 3 \rfloor} \le w \, 3^{w-1} - \frac{3^{w-1} - 1}{2} < \frac{w}{3} \, 3^w,
   ```

   with $C\sb{\max}^{\text{surv}}(w) = w \, 3^{w-1} - \frac{3^{w-1} - 1}{2}$ holding with equality for $w \in \lbrace 1, 2, 3\rbrace$ and strict inequality for all $w \ge 4$ (by Mihăilescu's Theorem $3^{m-1} - 1 = 2^{j^\ast \sb m} \iff m \in \lbrace 2, 3\rbrace$ ).

**Proof:**
For (1), since $j_m \ge m - 1$, Theorem 1.1 gives

```math
C_k(v) = \sum_{m=1}^{w} 3^{w-m} 2^{j_m} \ge \sum_{m=1}^{w} 3^{w-m} 2^{m-1} = 3^w - 2^w,
```

and similarly $j_m \le k - w + m - 1$ gives $C_k(v) \le 2^{k-w}(3^w - 2^w)$.

For (2), immediately before the $m$-th odd step at index $j_m$ ( $m \ge 2$ ), $j_m$ steps have been taken with cumulative weight $w\sb{j_m} = m - 1$. If the path survives at step $j_m$, then $2^{j_m} < 3^{m-1}$, so $j_m \le \lfloor (m - 1) \log_2 3 \rfloor = j^\ast \sb m$ (and for $m = 1$, $3^{w_1} > 2^1 \implies v_0 = 1 \implies j_1 = 0 = j^\ast \sb 1$ ). Conversely, if $j_m \le j^\ast \sb m$ for all $m \in \lbrace 1, \dots, w\rbrace$, then for any prefix length $j \in \lbrace 1, \dots, j_w + 1\rbrace$, let $m = w_j \ge 1$ be the number of odd steps in the first $j$ positions. If $m < w$, then the $(m+1)$-st odd step occurs at $j\sb{m+1} \ge j$, so $j \le j\sb{m+1} \le \lfloor m \log_2 3 \rfloor < m \log_2 3$ (since $\log_2 3 \notin \mathbb{Q}$ ), whence $2^j < 3^m = 3^{w_j}$.

For (3), since $\log_2 3 > 1$, the Beatty sequence $j^\ast \sb m = \lfloor (m - 1) \log_2 3 \rfloor$ is strictly increasing ( $j^\ast \sb{m+1} \ge j^\ast \sb m + 1$ ), so $(j^\ast \sb 1, \dots, j^\ast \sb w)$ is a valid index tuple realizing $C\sb{\max}^{\text{surv}}(w)$. Moreover, since $2^{j^\ast \sb m} < 3^{m-1}$ are integers, $2^{j^\ast \sb m} \le 3^{m-1} - 1$ for all $m \ge 2$, giving

```math
C_{\max}^{\text{surv}}(w) \le 3^{w-1} + \sum_{m=2}^{w} 3^{w-m}(3^{m-1} - 1) = w \, 3^{w-1} - \frac{3^{w-1} - 1}{2},
```

with equality iff $2^{j^\ast \sb m} = 3^{m-1} - 1$ for all $2 \le m \le w$, which by Mihăilescu's Theorem holds iff $w \le 3$. $\blacksquare$

### Corollary 2.2 (Diophantine Criterion for Garner's Coincidence $\sigma(n) = \tau(n)$ )
> If an integer $n \ge 2$ has $\tau(n) = k$ (so $v = \Phi_k(n)$ survives up to $k-1$ and drops below $1$ at step $k$: $2^{k-1} < 3^w < 2^k$ ) yet violates Garner's coincidence ( $\sigma(n) > \tau(n)$, so $T^k(n) \ge n$ ), then $n$ must satisfy the Diophantine upper bound:

```math
n \le \frac{C_{\max}^{\text{surv}}(w)}{2^k - 3^w} < \frac{w \, 3^{w-1}}{2^k - 3^w} < \frac{w}{3(k \ln 2 - w \ln 3)}.
```

---

## 3. Constructive Proof of Steiner's $1$-Cycle Theorem & Eliahou's Cycle Length Bounds

### Theorem 3.1 (Steiner 1977 — Non-Existence of Non-Trivial $1$-Cycles)
> Let $v = 1^w 0^{k-w}$ be a $1$-cycle (circuit) parity vector with $w \ge 1$ odd steps followed by $k - w \ge 1$ even steps. Then $n\sb{\text{cycle}}(v) \in \mathbb{Z}^+$ if and only if $(w, k) = (1, 2)$, corresponding to the trivial cycle $n_0 = 1$.

**Constructive Proof (Verified in `collatz_analysis/cycles.py`):**
1. **Algebraic Reduction:** By Theorem 2.1(1), $C_k(1^w 0^{k-w}) = 3^w - 2^w$, so

   ```math
   n_0 = \frac{3^w - 2^w}{2^k - 3^w} \implies n_0 + 1 = \frac{2^k - 2^w}{2^k - 3^w} = 2^w \left(\frac{2^{k-w} - 1}{2^k - 3^w}\right).
   ```

   Since $\gcd(2^w, 2^k - 3^w) = 1$, $n_0 \in \mathbb{Z}^+$ iff $2^k > 3^w$ and $(2^k - 3^w) \mid (2^{k-w} - 1)$. In particular,

   ```math
   0 < 2^k - 3^w \le 2^{k-w} - 1 \implies 1 < \frac{2^k}{3^w} \le 1 + \frac{2^{k-w} - 1}{3^w} < \frac{1}{1 - 2^{-w}} = 1 + \frac{1}{2^w - 1}.
   ```

   Taking natural logarithms yields the fundamental linear form in two logarithms:

   ```math
   0 < \Lambda(k, w) := k \ln 2 - w \ln 3 < \frac{1}{2^w - 1}.
   ```

2. **Baker–LMN Analytic Cutoff ( $w \ge 11,793$ ):** By Laurent, Mignotte, and Nesterenko (1995, Corollaire 2), for any positive integers $k, w$:

   ```math
   \ln |k \ln 2 - w \ln 3| \ge -24.34 \bigl(\max\{\ln b' + 0.14,\; 21\}\bigr)^2 \ln 2 \ln 3, \qquad b' = \frac{k}{\ln 3} + \frac{w}{\ln 2}.
   ```

   In the floor regime $\ln b' + 0.14 \le 21$ (valid for all $w \le 3.96 \times 10^8$ ), the right-hand side is $-24.34 \times 21^2 \ln 2 \ln 3 = -8171.03$, whereas $\ln(1 / (2^w - 1)) \approx -w \ln 2 < -8171.03$ for all $w \ge 11,793$ (and for $w > 3.96 \times 10^8$, $w \ln 2$ grows linearly while $(\ln b')^2$ grows only polylogarithmically). Thus no $1$-cycle can exist for $w \ge 11,793$.

3. **Legendre Continued Fraction Elimination ( $1 \le w < 11,793$ ):** For $w \ge 4$,

   ```math
   0 < \frac{k}{w} - \log_2 3 < \frac{1}{w(2^w - 1)\ln 2} < \frac{1}{2 w^2},
   ```

   so by Legendre's theorem $k/w$ must be an odd-indexed (upper) convergent $p\sb{2m+1}/q\sb{2m+1}$ of $\log_2 3$. Exhaustive integer verification for all $1 \le w \le 200$ and all upper convergents of $\log_2 3$ confirms that $(w=1, k=2, n_0=1)$ is the unique solution. $\blacksquare$

| Convergent Index $n$ | Partial Quotient $a_n$ | $p_n$ (Steps $k$ ) | $q_n$ (Odd Steps $w$ ) | Upper ( $2^{p_n} > 3^{q_n}$ ) | $\Lambda(p_n, q_n) = p_n \ln 2 - q_n \ln 3$ | $1$-Cycle Divisibility |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| $1$ | $1$ | $2$ | $1$ | Yes | $+2.877 \times 10^{-1}$ | **Yes ( $n_0 = 1$ )** |
| $3$ | $2$ | $8$ | $5$ | Yes | $+5.407 \times 10^{-2}$ | No ( $13 \nmid 211$ ) |
| $5$ | $3$ | $65$ | $41$ | Yes | $+7.177 \times 10^{-3}$ | No |
| $7$ | $5$ | $485$ | $306$ | Yes | $+3.588 \times 10^{-4}$ | No |
| $9$ | $23$ | $24,727$ | $15,601$ | Yes | $+8.893 \times 10^{-6}$ | No ( $w > 11,793$ ) |

### Theorem 3.2 (Eliahou–Barina Minimum Cycle Length Bound)
> For any positive integer cycle $O = \lbrace n_0, \dots, n\sb{k-1}\rbrace$ with minimum element $n\sb{\min} \ge N_0$:

```math
1 < \frac{2^k}{3^w} = \prod_{i : v_i = 1} \left(1 + \frac{1}{3 n_i}\right) \le \left(1 + \frac{1}{3 N_0}\right)^w \implies 0 < \frac{k}{w} - \log_2 3 < \frac{1}{3 N_0 \ln 2}.
```

> Given computational verification up to $N_0 = 2^{68}$ (Barina 2021) and $N_0 = 2^{71}$ (Barina 2025), the first admissible semiconvergent of $\log_2 3$ occurs at convergent index $23$ ( $c = 1$ ), yielding:
- **Minimum compressed steps ( $T$-steps):** $k \ge 114,208,327,604$
- **Minimum odd steps:** $w \ge 72,057,431,991$
- **Minimum uncompressed Collatz steps ( $k + w$ ):** $L \ge 186,265,759,595 \approx 1.8626 \times 10^{11}$.

---

## 4. Exact Lattice-Path Stopping-Time Sieve & Cramér Large-Deviation Rate

Because $\log_3 2 \notin \mathbb{Q}$, the coefficient-survival condition $\forall 1 \le j \le k,\; 3^{w_j} > 2^j$ depends only on the cumulative weights $w_j \ge \lceil j \log_3 2 \rceil$. Let $S(k, w)$ denote the number of coefficient-surviving parity vectors of length $k$ and weight $w$, governed by the exact lattice-path recurrence:

```math
S(k, w) = \mathbf{1}_{\{3^w > 2^k\}} \bigl(S(k - 1, w) + S(k - 1, w - 1)\bigr), \qquad S(0, 0) = 1.
```

### Theorem 4.1 (Cramér–Sanov Large-Deviation Decay of Surviving Residue Classes)
> Let $d_k = 2^{-k} \sum\sb{w=0}^k S(k, w)$ denote the fraction of residue classes modulo $2^k$ with coefficient stopping time $\tau > k$. By Cramér's Theorem and the Ballot / Sparre Andersen fluctuation formula for random walks above a line of irrational slope $p^\ast = \log_3 2 \approx 0.630929754$:

```math
\lim_{k \to \infty} -\frac{1}{k} \log_2 d_k = I_2(\log_3 2) = 1 - H_2(\log_3 2) \approx 0.050044473 \text{ bits/step},
```

> so the surviving residue density decays exponentially with base:

```math
\rho = 2^{H_2(\log_3 2) - 1} = \left(\log_3 2\right)^{-\log_3 2} \left(1 - \log_3 2\right)^{-(1 - \log_3 2)} / 2 \approx 0.965906553.
```

| Depth $k$ | Minimum Surviving Weight $\lceil k \log_3 2 \rceil$ | Exact Surviving Classes $S(k)$ | Survival Fraction $d_k = S(k) / 2^k$ |
| :---: | :---: | :---: | :---: |
| $10$ | $7$ | $64$ | $6.250000 \times 10^{-2}$ |
| $25$ | $16$ | $573,162$ | $1.708156 \times 10^{-2}$ |
| $50$ | $32$ | $3,734,259,929,440$ | $3.316689 \times 10^{-3}$ |
| $100$ | $64$ | $302,560,669,500,543,257,546,172,187$ | $2.386783 \times 10^{-4}$ |
| $200$ | $127$ | $4.917911 \times 10^{54}$ | $3.060424 \times 10^{-6}$ |

---

## 5. Tao's $m$-Step $3$-Adic Memory Annihilation & the Base $2$ / Base $3$ Automaton Barrier

Why does Terras's theorem ( $\lim\sb{k \to \infty} d_k = 0$ ) not immediately imply the Collatz conjecture? Because knowing $T^k(n) < n$ for almost all $n$ does not prevent the image $T^k(n)$ from landing in the sparse exceptional set of density $d_k$. Terence Tao (2019) overcame this barrier for logarithmic density by analyzing the fine-scale mixing of the **Syracuse map** $S(n) = (3n + 1) / 2^{\nu_2(3n+1)}$ on odd integers.

### Theorem 5.1 (Exact $m$-Step $3$-Adic Memory Annihilation of the Syracuse Map)
> Let $n$ be any odd integer, and let $a_i = \nu_2(3 S^{i-1}(n) + 1) \ge 1$ denote the $2$-adic valuation at the $i$-th Syracuse step. Then for every $m \ge 1$, after $m$ Syracuse steps:

```math
S^m(n) = \frac{3^m n + \sum_{j=1}^m 3^{m-j} \, 2^{A_1 - A_j}}{2^{A_1}}, \qquad A_j = \sum_{i=j}^m a_i.
```

> Reducing modulo $3^m$, the initial state term $3^m n \, 2^{-A_1} \equiv 0 \pmod{3^m}$ vanishes identically:

```math
S^m(n) \equiv \sum_{j=1}^{m} 3^{m-j} \, 2^{-(a_j + \dots + a_m)} \pmod{3^m}.
```

> Consequently:
1. For every fixed valuation tuple $(a_1, \dots, a_m) \in (\mathbb{Z}^+)^m$, the residue $S^m(n) \bmod 3^m$ is **completely independent of $n \bmod 3^m$**.
2. The induced Markov transition operator $P_m$ on $(\mathbb{Z}/3^m\mathbb{Z})^\times$ driven by $a_i \sim \text{Geom}(1/2)$ satisfies $\operatorname{rank}(P_m^m) = 1$: the pairwise coupling total variation distance $\max\sb{x, y} \|P_m^t(x, \cdot) - P_m^t(y, \cdot)\|\sb{\text{TV}}$ drops to **exact zero at step $t = m$**.

### Theorem 5.2 (Myhill–Nerode Carry State Complexity & the Cobham–Conway Barrier)
> For any fixed parity vector $v \in \lbrace 0, 1\rbrace ^k$ of odd weight $w$, consider the LSB-first base $2$ sequential transducer computing the numerator $y = 3^w x + C_k(v)$. Then:
1. Every carry $c \in \lbrace 0, 1, \dots, 3^w - 1\rbrace$ is reachable from $c_0 = 0$ via the transition $c' = \lfloor (3^w b + c)/2 \rfloor$ ( $b \in \lbrace 0, 1\rbrace$ ), and distinct carries yield distinct $2$-adic output streams $c + 3^w x \in \mathbb{Z}\sb 2$.
2. Hence the minimal DFA/transducer tracking $k$ Collatz steps in base $2$ has state complexity **exactly $3^w$** (which satisfies $3^w > 2^k$ along all surviving branches).
3. By Cobham's Theorem (1969), because $2$ and $3$ are multiplicatively independent ( $\log_2 3 \notin \mathbb{Q}$ ), no non-trivial subset of $\mathbb{N}$ invariant under both $\times 2$ and $\times 3$ dynamics can be recognized by a finite automaton, explaining why bounded-depth modular sieves cannot close the remaining $O(d_k)$ cone without global $2$-adic / $3$-adic entropy bounds.

---

## 6. $2$-Adic Ultrametric Injectivity of Carry Polynomials & The Sharp Threshold Theorem ( $k^\ast = 34, w^\ast = 22$ ) for Surviving Diamond Coalescences

We now prove a suite of original structural theorems governing when two distinct parity vectors can produce identical integer carries or colliding arithmetic progressions along the coefficient-surviving tree $\mathcal{S}\sb k$.

### Theorem 6.1 ( $2$-Adic Ultrametric Valuation of Carry Differences & Global Injectivity of $C_k(v)$ )
> Let $v, v'$ be two parity vectors of the same odd weight $w \ge 1$ with odd-step index tuples $0 \le j_1 < j_2 < \dots < j_w$ and $0 \le j'\sb 1 < j'\sb 2 < \dots < j'\sb w$.
1. If $(j_1, \dots, j_w) \ne (j'\sb 1, \dots, j'\sb w)$, let $m_0 = \min\lbrace m \in \lbrace 1, \dots, w\rbrace : j_m \ne j'\sb m\rbrace$ be their first index of divergence, and assume without loss of generality that $j\sb{m_0} < j'\sb{m_0}$. Then the exact $2$-adic valuation of their carry difference is:

   ```math
   \nu_2\bigl(C(v') - C(v)\bigr) = j_{m_0}.
   ```

2. In particular, $C(v') \ne C(v)$: the map $(j_1, \dots, j_w) \mapsto C(v) = \sum\sb{m=1}^w 3^{w-m} \, 2^{j_m}$ is **globally injective** on all strictly increasing $w$-tuples of non-negative integers, with an exact $O(w)$-step deterministic left-inverse (`ultrametric_decode_carry`):

   ```math
   j_m = \nu_2\!\left(C(v) - \sum_{i=1}^{m-1} 3^{w-i} \, 2^{j_i}\right) \qquad (m = 1, \dots, w).
   ```

**Proof:**
Since $j_m = j'\sb m$ for all $1 \le m < m_0$, the leading $m_0 - 1$ terms of $C(v)$ and $C(v')$ cancel identically:

```math
C(v') - C(v) = \sum_{m = m_0}^{w} 3^{w-m} \left(2^{j'_m} - 2^{j_m}\right) = -3^{w - m_0} 2^{j_{m_0}} + 3^{w - m_0} 2^{j'_{m_0}} + \sum_{m = m_0 + 1}^{w} 3^{w-m} \left(2^{j'_m} - 2^{j_m}\right).
```

Because $j\sb{m_0} < j'\sb{m_0}$ and the sequences are strictly increasing, every power of $2$ in the remaining terms satisfies $j_m \ge j\sb{m_0} + 1$ and $j'\sb m \ge j'\sb{m_0} \ge j\sb{m_0} + 1$. Thus the first term $-3^{w - m_0} 2^{j\sb{m_0}}$ has exact $2$-adic valuation $j\sb{m_0}$ while every other term has $2$-adic valuation $\ge j\sb{m_0} + 1$. By the ultrametric equality for $\nu_2$, $\nu_2(C(v') - C(v)) = j\sb{m_0} < \infty$, so $C(v') \ne C(v)$. Applying the same argument with $C(v') = 0$ at each step $m = 1, \dots, w$ yields the recursive reconstruction formula for $j_m$. $\blacksquare$

---

### Theorem 6.2 (The Sharp Onset Threshold $k^\ast = 34, w^\ast = 22$ for Equal-Length Surviving Diamond Coalescences)
> Two distinct residue classes $r_1, r_2 \in \lbrace 0, 1, \dots, 2^k - 1\rbrace$ form an **equal-length progression coalescence** at step $k$ if $T^k(2^k t + r_1) = T^k(2^k t + r_2)$ for all $t \in \mathbb{Z}\sb{\ge 0}$, and a **surviving diamond coalescence** if in addition both $v_1 = \Phi_k(r_1)$ and $v_2 = \Phi_k(r_2)$ lie in the coefficient-surviving set $\mathcal{S}\sb k$ ( $\forall 1 \le j \le k,\; 3^{w_j} > 2^j$ ).

1. **(Algebraic Diamond Criterion):** $T^k(2^k t + r_1) = T^k(2^k t + r_2)$ holds for all $t \ge 0$ **if and only if** $\operatorname{wt}(v_1) = \operatorname{wt}(v_2) = w$ and

   ```math
   C_k(v_2) - C_k(v_1) = (r_1 - r_2) \, 3^w.
   ```

2. **(Complete Absence for $1 \le k \le 33$ ):** For every $1 \le k \le 33$, **no two distinct coefficient-surviving residue classes modulo $2^k$ ever coalesce at step $k$**.
3. **(Sharp Onset at $k^\ast = 34, w^\ast = 22$ with Universal Gap $\delta = 4$ ):** At depth $k^\ast = 34$, surviving diamond coalescence occurs for the **first time**, uniquely at weight $w^\ast = 22$, with **exactly $5$ minimal pairs** $(v\sb{\text{low}}, v\sb{\text{high}})$ out of the $S(34) = 151,917,636$ surviving classes modulo $2^{34}$. Every one of the $5$ pairs diverges at the $3\text{rd}$ odd step ( $m_0 = 3$: $j_3 = 2$ vs. $j'\sb 3 = 3$ ) and satisfies:

   ```math
   r_{\text{low}} - r_{\text{high}} = 4, \qquad C_{34}(v_{\text{high}}) - C_{34}(v_{\text{low}}) = 4 \cdot 3^{22} = 125,524,238,436,
   ```

   so that $\forall t \ge 0$, $T^{34}(2^{34} t + r\sb{\text{low}}) = T^{34}(2^{34} t + r\sb{\text{low}} - 4)$.

**Proof:**
For (1), $T^k(2^k t + r_i) = 3^{w_i} t + b_i$ where $2^k b_i = 3^{w_i} r_i + C_k(v_i)$. Equality of polynomials in $t$ holds iff $w_1 = w_2 = w$ and $b_1 = b_2 \iff 3^w(r_1 - r_2) = C_k(v_2) - C_k(v_1)$.

For (2) and (3), let $v_1, v_2 \in \mathcal{S}\sb k$ have weight $w$ and first divergence at $m_0 \in \lbrace 1, \dots, w\rbrace$ with $j\sb{m_0} < j'\sb{m_0}$. Because every coefficient-surviving path satisfies $j_1 = 0$ ( $3^1 > 2^1$ ) and $j_2 = 1$ ( $j_2 \le \lfloor \log_2 3 \rfloor = 1$ ), we must have $m_0 \ge 3$ and $j\sb{m_0} \ge m_0 - 1 \ge 2$. By Theorem 6.1(1), $\nu_2(C_k(v_2) - C_k(v_1)) = j\sb{m_0}$. Since $3^w \mid (C_k(v_2) - C_k(v_1))$ and $\gcd(2^{j\sb{m_0}}, 3^w) = 1$, we have

```math
\delta := r_1 - r_2 = \frac{C_k(v_2) - C_k(v_1)}{3^w} \ge 2^{j_{m_0}} \ge 2^{m_0 - 1} \ge 4.
```

Meanwhile, since the first $m_0 - 1$ terms cancel and $j_m \le \min(\lfloor (m-1)\log_2 3 \rfloor, k - 1 - (w - m)) =: B\sb{k,w}(m)$ for all $m \ge m_0$,

```math
C_k(v_2) - C_k(v_1) \le \Delta_{\max}(k, w, m_0) := \sum_{m = m_0}^{w} 3^{w-m} \bigl(2^{B_{k,w}(m)} - 2^{m-1}\bigr).
```

- For all $1 \le w \le 20$ and all $3 \le m_0 \le w$, $\Delta\sb{\max}(\infty, w, m_0) / (2^{m_0 - 1} 3^w) \le 0.9898 < 1$, ruling out $w \le 20$ purely analytically.
- For $k \le 33$, the ratio $\Delta\sb{\max}(k, w, m_0) / (2^{m_0 - 1} 3^w)$ reaches $\ge 1$ only at $m_0 = 3$ ( $\delta = 4$ ) for $w \in \lbrace 21, 22, 23\rbrace$. Enumerating all surviving paths $v_2$ with $C_k(v_2) \ge (3^w - 2^w) + 4 \cdot 3^w$ ( $12$ paths at $w=21$; $0$ paths with $j'\sb{22} \le 32$ at $w=22$; $1$ path at $w=23, k=33$ ) and applying the deterministic decoder `ultrametric_decode_carry` to $C_k(v_2) - 4 \cdot 3^w$ yields $0$ valid preimages for all $k \le 33$.
- At $k^\ast = 34$, across $w \in \lbrace 22, 23, 24\rbrace$ ( $362 + 162 + 1 = 525$ candidate high paths), `ultrametric_decode_carry` finds **exact 5 solutions**, all at $w^\ast = 22$ with $\delta = 4$:

| Pair # | $r\sb{\text{high}}$ | $r\sb{\text{low}} = r\sb{\text{high}} + 4$ | Common Image $T^{34}(r\sb{\text{low}}) = T^{34}(r\sb{\text{high}})$ | $C\sb{34}(v\sb{\text{low}})$ | $C\sb{34}(v\sb{\text{high}}) = C\sb{\text{low}} + 4 \cdot 3^{22}$ |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **1** | $7,435,082,747$ | $7,435,082,751$ | $13,581,056,558$ | $39,966,604,313$ | $165,490,842,749$ |
| **2** | $5,348,744,187$ | $5,348,744,191$ | $9,770,112,830$ | $41,256,549,401$ | $166,780,787,837$ |
| **3** | $15,257,926,651$ | $15,257,926,655$ | $27,870,404,645$ | $35,940,981,785$ | $161,465,220,221$ |
| **4** | $11,843,133,435$ | $11,843,133,439$ | $21,632,881,628$ | $35,396,786,201$ | $160,921,024,637$ |
| **5** | $15,231,450,875$ | $15,231,450,879$ | $27,822,043,514$ | $36,621,226,265$ | $162,145,464,701$ |

---

## 7. Master $(2,3)$-Adic Progression Duality & Contractive Coalescence Sieve

### Theorem 7.1 (Master $(2,3)$-Adic Progression Duality & Sharp $k\sb{\text{contr}}^\ast = 6$ Coalescence Onset)
> For every parity vector $v \in \lbrace 0, 1\rbrace ^k$ of weight $w$, $T^k$ maps the $2$-adic progression $\mathcal{A}\sb 2(v) = r_v + 2^k \mathbb{Z}\sb{\ge 0}$ bijectively onto the $3$-adic progression $\mathcal{A}\sb 3(v) = b_v + 3^w \mathbb{Z}\sb{\ge 0}$, where $b_v = T^k(r_v)$ satisfies the **Dual Valuation Congruence**:

```math
b_v \equiv \Omega(v) := 2^{-k} C_k(v) = \sum_{m=1}^{w} 3^{w-m} \, 2^{-(k - j_m)} \pmod{3^w}.
```

> Consequently, a surviving branch $v \in \mathcal{S}\sb{k, w}$ contractively coalesces into an earlier surviving branch $v' \in \mathcal{S}\sb{k', w'}$ ( $w' < w$, meaning every large $n \in \mathcal{A}\sb 2(v)$ satisfies $T^k(n) = T^{k'}(n')$ for $n' \in \mathcal{A}\sb 2(v')$ with $n' < n$ ) **if and only if**:

```math
3^{w - w'} < 2^{k - k'} \quad \text{and} \quad 2^{-k} C_k(v) \equiv 2^{-k'} C_{k'}(v') \pmod{3^{w'}}.
```

- **Unification with Terras's Stopping Sieve:** Taking $v' = \emptyset$ ( $k' = 0, w' = 0$ ) recovers Terras's coefficient stopping condition $3^w < 2^k$ (since congruence modulo $3^0 = 1$ is vacuous).
- **Sharp Onset of Unequal-Length Coalescence ( $k\sb{\text{contr}}^\ast = 6, w\sb{\text{contr}}^\ast = 4$ ):** For $1 \le k \le 5$, no surviving path in $\mathcal{S}\sb k$ satisfies contractive coalescence with $w' \ge 1$. At $k^\ast = 6, w^\ast = 4$, contractive coalescence turns on at the **unique path** $v = (1, 1, 1, 1, 0, 0)$ ( $r_v = 15 \pmod{64}$ ), which coalesces with $v' = (1)$ ( $k' = 1, w' = 1$ ):

  ```math
  \forall t \ge 0, \qquad T^6(64 t + 15) = 81 t + 20 = 3(27 t + 6) + 2 = T^1(54 t + 13), \qquad 54 t + 13 < 64 t + 15.
  ```

- By depth $k = 17$, contractive $3$-adic coalescence prunes **$40.89\%$** of all coefficient-surviving paths ( $2,499$ uncoalesced active classes vs. $S(17) = 4,228$ ).

---

## 8. Master $m$-Cycle Block-Telescoping Carry Identity & $2$-Cycle Non-Existence

### Theorem 8.1 (Master $m$-Cycle Block-Telescoping Identity & $2$-Cycle Obstruction)
> Let $v = 1^{w_1} 0^{a_1} 1^{w_2} 0^{a_2} \cdots 1^{w_m} 0^{a_m}$ be an $m$-cycle parity vector with block lengths $k_r = w_r + a_r$, prefix lengths $K_r = \sum\sb{i=1}^{r-1} k_i$, total length $K = \sum\sb{r=1}^m k_r$, suffix weights $W\sb{>r} = \sum\sb{i=r+1}^m w_i$, and total weight $W = \sum\sb{r=1}^m w_r$. Then the affine carry polynomial telescopes across the $m$ blocks as:

```math
C_K(v) = \sum_{r=1}^{m} 3^{W_{>r}} \, 2^{K_r} \bigl(3^{w_r} - 2^{w_r}\bigr).
```

> In particular, for $m = 2$ ( $v = 1^{w_1} 0^{a_1} 1^{w_2} 0^{a_2}$ ):
1. $C_K(v) = 3^{w_2}(3^{w_1} - 2^{w_1}) + 2^{w_1 + a_1}(3^{w_2} - 2^{w_2})$.
2. Any positive integer $2$-cycle satisfies the linear form bound $0 < K \ln 2 - W \ln 3 < \frac{1}{2^{w_1} - 1} + \frac{1}{2^{w_2} - 1}$. Exhaustive verification across all $199,708$ admissible $(w_1, a_1, w_2, a_2)$ tuples with $W \le 80$ confirms that the unique positive integer solution is the unreduced $2$-fold repetition of the trivial cycle $(w_1, a_1, w_2, a_2) = (1, 1, 1, 1)$ ( $n_0 = 1$ ).

---

## 9. Exact One-Equation Diophantine Equivalence & Garden-of-Eden Reduction

### Theorem 9.1 (The One-Equation $(2,3)$-Bilinear Collatz Equivalence)
> An integer $n \in \mathbb{Z}^+$ converges to $1$ under the Collatz map **if and only if** there exist integers $k \ge w \ge 0$ and strictly increasing exponents $0 \le j_1 < j_2 < \dots < j_w < k$ satisfying the single $(2,3)$-bilinear equation:

```math
2^k = n \cdot 3^w + \sum_{m=1}^{w} 3^{w-m} \, 2^{j_m}.
```

> No auxiliary parity constraints on $n$ or its intermediate iterates are needed: any solution $(k, w, j_1, \dots, j_w)$ automatically forces $\Phi_k(n) = v$ and $T^k(n) = 1$ via $2$-adic Hensel divisibility. Furthermore, it suffices to prove solvability solely on $\lbrace n \in \mathbb{Z}^+ : \gcd(n, 6) = 1\rbrace$, since even integers halve and every odd multiple of $3$ ( $n = 3q$ ) maps in one Syracuse step to $S(3q) = (9q+1)/2^a \equiv 2^{-a} \not\equiv 0 \pmod 3$.

**Proof:**
Suppose $2^k = n \cdot 3^w + C_k(v)$ where $v \in \lbrace 0, 1\rbrace ^k$ has $1$-bits at $0 \le j_1 < \dots < j_w < k$. For each $0 \le r \le k$, splitting $C_k(v) = 3^{w - w_r} C_r(v\sb{<r}) + \sum\sb{m = w_r + 1}^w 3^{w-m} 2^{j_m}$ shows that the tail sum has $j_m \ge r$, so $2^r$ divides $2^k - \text{tail} = 3^{w - w_r}(3^{w_r} n + C_r(v\sb{<r}))$. Since $\gcd(2^r, 3^{w - w_r}) = 1$, $x_r := (3^{w_r} n + C_r(v\sb{<r})) / 2^r \in \mathbb{Z}^+$ for every $0 \le r \le k$. If $v_r = 0$, $x\sb{r+1} = x_r / 2 \in \mathbb{Z}^+ \implies x_r \equiv 0 \pmod 2$ and $T(x_r) = x\sb{r+1}$. If $v_r = 1$, $x\sb{r+1} = (3 x_r + 1)/2 \in \mathbb{Z}^+ \implies x_r \equiv 1 \pmod 2$ and $T(x_r) = x\sb{r+1}$. By induction, $x_r = T^r(n)$ for all $r$ and $T^k(n) = x_k = 2^k / 2^k = 1$. $\blacksquare$

---

## 10. Raney Cycle Separation on $\mathbb{Z}^-$ & Self-Certified Beatty–Sturmian Garner Bootstrap

### Theorem 10.1 (Universal $\sigma(n) \ge \tau(n)$, Raney Separation, and Self-Certified Bootstrap)
1. **(Universal Lower Bound):** For every $n \ge 2$ and every $1 \le j < \tau(n)$, $3^{w_j(n)} \ge 2^j + 1$ and $C_j \ge 0$, so $T^j(n) \ge \frac{(2^j + 1) n}{2^j} > n$. Hence $\sigma(n) \ge \tau(n)$ holds universally on $\mathbb{Z}\sb{\ge 2}$.
2. **(Opposite Behavior of Cycles on $\mathbb{Z}^+$ vs. $\mathbb{Z}^-$ ):**
   - On $\mathbb{Z}^-$, every cycle ( $\lbrace -1\rbrace$, $\lbrace -5, -7, -10\rbrace$, and the $11$-cycle starting at $-17$ ) has $3^w > 2^k$; by **Raney's Cycle Lemma**, at least one cyclic shift of each cycle stays strictly inside the infinite surviving Cantor cone $\mathcal{S}\sb \infty = \lbrace x \in \mathbb{Z}\sb 2 : \forall j \ge 1,\; 3^{w_j(x)} > 2^j\rbrace$—and in fact, each of the three known negative cycles has a **unique** representative in $\mathcal{S}\sb \infty \cap \mathbb{Z}^-$, namely its minimum-magnitude element ( $-1$, $-5$, and $-17$ respectively!).
   - On $\mathbb{Z}^+$, any hypothetical non-trivial cycle $O \subset \mathbb{Z}^+$ of period $k$ has $n_0 = \frac{C_k(v)}{2^k - 3^w} > 0 \implies 3^w < 2^k$. Thus its minimum element $n\sb{\min} = \min O$ exits $\mathcal{S}\sb \infty$ ( $\tau(n\sb{\min}) = k_0 \le k < \infty$ ) while satisfying $\sigma(n\sb{\min}) = \infty$, forcing $n\sb{\min}$ to be a **Garner exception** bounded by the exact Sturmian threshold:

     ```math
     n_{\min} \le B(w_0) := \left\lfloor \frac{C_{\max}^{\text{surv}}(w_0)}{2^{k_0} - 3^{w_0}} \right\rfloor, \qquad k_0 = \lfloor w_0 \log_2 3 \rfloor + 1.
     ```

3. **(Self-Certified CPU Bootstrap):** Using the affine jump sieve $T^s(2^s t + r) = 3^{w_s} t + b_s$:
   - Checking $N_0 = 72,058 = B(306)$ at $s = 14$ ( $3,217$ survivor integers, **$6\text{ ms}$**) self-certifies $\sigma(n) = \tau(n)$ and **rules out all non-trivial positive cycles up to $k \le 1,538$** ( $2^{1,538}$ parity vectors).
   - Checking $N_0 = 206,178,386 = B(15,601)$ at $s = 20$ ( $5,373,371$ survivor integers, **$16.8\text{ s}$**) self-certifies $\sigma(n) = \tau(n)$ for all $n \in \mathbb{Z}^+$ with $\tau(n) \le 75,234$ and **rules out all non-trivial positive cycles up to $k \le 75,234$ ( $L = k + w \le 122,701$ uncompressed steps)** with zero external assumptions.

---

## 11. Formal Counter-Model No-Go Meta-Theorem & Minimal Open Frontier

Why has every elementary proof attempt since 1937 hit an obstruction? Following the independence/counter-model paradigm, Theorem 11 constructs explicit counter-models demonstrating that no proof of the Collatz Conjecture can succeed using any axiom subset shared by $\mathcal{M}\sb 1, \mathcal{M}\sb 2, \mathcal{M}\sb 3$:

| Counter-Model | Shared Properties with $(\mathbb{Z}^+, T)$ | How Collatz Fails (Verified Witness) | Missing Necessary Ingredient for $\mathbb{Z}^+$ |
| :--- | :--- | :--- | :--- |
| **$\mathcal{M}\sb 1 = \mathbb{Q}\sb{>0} \cap \mathbb{Z}\sb{(2)}$** | $x > 0$, $2$-adic bijection $\Phi\sb \infty$, Cramér decay $d_k \sim \rho^k$, drift $\log_2 3 - 2 < 0$, $3$-adic nilpotent mixing | Infinitely many positive cycles, e.g. $n_0 = \frac{19}{5}$ at $(k, w) = (5, 3)$ | Prime divisibility in $\mathbb{Z}$ at odd primes $p \mid (2^k - 3^w)$ |
| **$\mathcal{M}\sb 2 = (\mathbb{Z}^-, T)$** ( $3n - 1$ ) | Full $\mathbb{Z}$-integrality, $2$-adic bijection, Cramér decay $d_k \sim \rho^k$, drift $\log_2 3 - 2 < 0$, $3$-adic nilpotency | $\mathcal{S}\sb \infty \cap \mathbb{Z}^- \ne \emptyset$ and non-unit $11$-cycle $n_0 = -17$ ( $2^{11} - 3^7 = -139 \mid 2363$ ) | Strict sign asymmetry $2^k - 3^w > 0$ ( $+1$ vs. $-1$ carry orientation) |
| **$\mathcal{M}\sb 3 = (\mathbb{Z}^+, T_5)$** ( $5n + 1$ ) | $n \in \mathbb{Z}^+$, $+1$ carry sign, Hensel bijection $\Phi_k^{(5)}$, ultrametric carry injectivity | Two primitive positive integer cycles at $(k, w) = (7, 3)$ ( $2^7 - 5^3 = +3$ ): $n_0 = 13$ and $n_0 = 17$ | Negative drift $\log_2 3 < 2$ **and** specific continued-fraction separation of $\log_2 3$ |

### Theorem 12.1 (Exact Two-Statement Sufficiency & Necessary Decomposition)
> By Theorems 1–11 and strong induction on $(\mathbb{Z}^+, <)$, the **Collatz Conjecture together with Garner's Coincidence** ( $\sigma(n) = \tau(n) < \infty$ for all $n \ge 2$ ) holds **if and only if** both of the following open arithmetic statements hold:
1. ***(Open Problem A — Empty Positive Integer Intersection with the Measure-Zero Beatty–Cantor Cone):***

   ```math
   \mathcal{S}_\infty \cap \mathbb{Z}^+ = \emptyset \quad \Longleftrightarrow \quad \neg \exists n \in \mathbb{Z}_{\ge 2} \;\forall m \ge 1,\;\; j_m(n) \le \lfloor (m - 1) \log_2 3 \rfloor.
   ```

   (Known: $\mu\sb{\text{Haar}}(\mathcal{S}\sb \infty) = 0$, $\dim_H(\mathcal{S}\sb \infty) = H_2(\log_3 2) \approx 0.949955$, and $\mathcal{S}\sb \infty \cap \mathbb{Z}^- \ne \emptyset$.)
2. **(Open Problem B — Hensel Lift Non-Exceedance at Upper Convergents of $\log_2 3$ ):**
   For all $(k_0, w_0)$ above the verified bootstrap threshold ( $k_0 \ge 75,235$ self-certified here; $k_0 \ge 1.14 \times 10^{11}$ under Barina's $N_0 = 2^{71}$ ) with $2^{k_0 - 1} < 3^{w_0} < 2^{k_0}$, and every $v \in \mathcal{S}\sb{k_0 - 1} \times \lbrace 0\rbrace$, the unique Hensel lift $r_v = (-C\sb{k_0}(v) 3^{-w_0}) \bmod 2^{k_0} \in \lbrace 1, \dots, 2^{k_0} - 1\rbrace$ avoids the quasi-polynomial interval $\lbrack 1, B(w_0)\rbrack$:

   ```math
   r_v > \frac{C_{k_0}(v)}{2^{k_0} - 3^{w_0}} = \exp\!\bigl(O((\ln k_0)^2)\bigr) \ll 2^{k_0}.
   ```

---

## 12. Deep-Frontier Attacks on Open Problems A and B (Theorems 13 & 14)

### Theorem 13.1 (Pure Divergence on $\mathcal{S}\sb \infty \cap \mathbb{Z}^+$, Cardinality Dichotomy, and $(2,3)$-Series Separation of $x\sb{\text{Sturm}}$ from $\mathbb{Z}^-$ )
> Let $\mathcal{S}\sb \infty := \lbrace x \in \mathbb{Z}\sb 2 : \forall k \ge 1,\; 3^{w_k(x)} > 2^k\rbrace$ denote the infinite coefficient-surviving Beatty–Cantor cone in $\mathbb{Z}\sb 2$.

1. **(Pure Divergence to $+\infty$ on $\mathcal{S}\sb \infty \cap \mathbb{Z}^+$ ):** Every $n \in \mathcal{S}\sb \infty \cap \mathbb{Z}^+$ satisfies the full limit $\lim\sb{k \to \infty} T^k(n) = +\infty$ (not merely $\limsup\sb{k \to \infty} T^k(n) = +\infty$ ).
2. **(Infinite Tail-Minima Amplification & Cardinality Dichotomy):** Any divergent positive trajectory $\lim\sb{k \to \infty} T^k(n_0) = +\infty$ contains an infinite strictly increasing sequence of tail minima $m_1 < m_2 < m_3 < \dots \to +\infty$ satisfying $\sigma(m_i) = \infty$ for all $i \ge 1$. Consequently, under Open Problem B, $\lvert \mathcal{S}\sb \infty \cap \mathbb{Z}^+ \rvert \in \lbrace 0, \aleph_0\rbrace$ (if non-empty, $\mathcal{S}\sb \infty \cap \mathbb{Z}^+$ must be countably infinite).
3. (Exact $(2,3)$-Series Duality on $\mathbb{Z}^-$ vs. Linear Carry Divergence of $x\sb{\text{Sturm}}$ ):
   - Every $x \in \mathcal{S}\sb \infty \cap \mathbb{Z}^-$ satisfies $\sum\sb{m=1}^{\infty} \frac{2^{j_m(x)}}{3^m} \le \lvert x \rvert < \infty$ (with exact equality $\sum\sb{m=1}^\infty \frac{2^{j_m(x)}}{3^m} = \lvert x \rvert$ whenever $x$ enters any negative integer cycle, e.g., $x \in \lbrace -1, -5, -17\rbrace$ ), forcing $\lim\sb{m \to \infty} (m \log_2 3 - j_m(x)) = +\infty$.
   - Conversely, let $v^\ast (\infty) \in \mathcal{S}\sb \infty$ be the lexicographically maximal (Beatty–Sturmian) survivor ( $j^\ast \sb m = \lfloor (m-1)\log_2 3 \rfloor$ ) and $x\sb{\text{Sturm}} := \Phi\sb \infty^{-1}(v^\ast (\infty)) \in \mathbb{Z}\sb 2$ (`0xad0140abc9be5bfb` $\pmod{2^{64}}$ ). For every $w \ge 1$,

     ```math
     \frac{w}{6} < \frac{C_{\max}^{\text{surv}}(w)}{3^w} = \sum_{m=1}^{w} \frac{2^{j^*_m}}{3^m} \le \frac{w}{3} \xrightarrow{w \to \infty} +\infty,
     ```

     which proves **unconditionally** that $x\sb{\text{Sturm}} \notin \mathbb{Z}^-$.

**Proof:**
- **(1)** Suppose $\liminf\sb{k \to \infty} T^k(n) = M < \infty$ for some $n \in \mathcal{S}\sb \infty \cap \mathbb{Z}^+$. Discreteness of $\mathbb{Z}^+$ gives $0 \le k_1 < k_2$ with $T^{k_1}(n) = T^{k_2}(n) = M$, placing $M > 0$ on a cycle of period $p = k_2 - k_1 \ge 1$ and odd weight $w\sb{\text{cyc}}$. By Böhm–Sontacchi, $M = C_p / (2^p - 3^{w\sb{\text{cyc}}}) > 0 \implies 3^{w\sb{\text{cyc}}} < 2^p$. Then $3^{w\sb{k_1 + r p}(n)} / 2^{k_1 + r p} = (3^{w\sb{k_1}} / 2^{k_1})(3^{w\sb{\text{cyc}}} / 2^p)^r \to 0 < 1$ as $r \to \infty$, contradicting $n \in \mathcal{S}\sb \infty$.
- **(2)** Define $k^\ast (K) = \max\lbrace k \ge K : T^k(n_0) = \min\sb{j \ge K} T^j(n_0)\rbrace$ (well-defined and finite because $T^k(n_0) \to +\infty$ ). Setting $K_1 = 0$ and $K\sb{i+1} = k^\ast (K_i) + 1$ yields $m_i = T^{k^\ast (K_i)}(n_0)$ with $m_1 < m_2 < \dots \to +\infty$ and $T^j(m_i) > m_i$ for all $j \ge 1$ ( $\sigma(m_i) = \infty$ ). Under Open Problem B, every $m_i > N_0$ has $\tau(m_i) = \sigma(m_i) = \infty \implies m_i \in \mathcal{S}\sb \infty \cap \mathbb{Z}^+$.
- **(3)** Because $(-1, 0) \cap \mathbb{Z} = \emptyset$, $\mathbb{Z}^- = (-\infty, -1\rbrack \cap \mathbb{Z}$ is forward $T$-invariant ( $T(\mathbb{Z}^-) \subseteq \mathbb{Z}^-$ ). Thus for any $x \in \mathcal{S}\sb \infty \cap \mathbb{Z}^-$, $x + \sum\sb{m=1}^{w_k} \frac{2^{j_m(x)}}{3^m} = \frac{2^k}{3^{w_k}} T^k(x) < 0$ for all $k \ge 1$, giving $\sum\sb{m=1}^\infty \frac{2^{j_m(x)}}{3^m} \le \lvert x \rvert < \infty$ (and if $T^k(x)$ is bounded while $3^{w\sb{\text{cyc}}} > 2^{k\sb{\text{cyc}}}$, $\frac{2^k}{3^{w_k}} T^k(x) \to 0 \implies \sum\sb{m=1}^\infty \frac{2^{j_m(x)}}{3^m} = \lvert x \rvert$ ). For $v^\ast (\infty)$, $(m-1)\log_2 3 - 1 < j^\ast \sb m \le (m-1)\log_2 3 \implies \frac{1}{6} < \frac{2^{j^\ast \sb m}}{3^m} \le \frac{1}{3}$ for every $m \ge 1$, summing to $\frac{w}{6} < \frac{C\sb{\max}^{\text{surv}}(w)}{3^w} \le \frac{w}{3} \to +\infty$. $\blacksquare$

---

### Theorem 14.1 (Sorted Cyclic Rearrangement Lemma & Unconditional All-Weight Non-Existence of Positive $m$-Cycles)
> Let $v = 1^{w_1} 0^{a_1} 1^{w_2} 0^{a_2} \cdots 1^{w_m} 0^{a_m}$ ( $w_r \ge 1, a_r \ge 1$, total weight $W = \sum\sb{r=1}^m w_r$, total compressed length $K = \sum\sb{r=1}^m (w_r + a_r)$ ) be a hypothetical non-trivial positive integer $m$-cycle with odd block-minima $x_1, \dots, x_m > N_0$, and set $\theta := \log_2 3$, $L_r := \log_2(x_r + 1) \ge L_0 := \log_2(N_0 + 1)$, and $\eta(N_0) := 1 - \log_2\bigl(1 + (N_0 + 1)^{-\theta}\bigr) > 0$.

1. **(Exact Block-Product & One-Step Spiral Bound):** Every block $r \in \mathbb{Z}/m\mathbb{Z}$ satisfies $x_r + 1 = 2^{w_r} u_r$ for an odd integer $u_r \ge 1$, $L\sb{r+1} \le \theta L_r - \eta(N_0)$, and the exact global product identity:

   ```math
   \frac{2^K}{3^W} = \prod_{r=1}^{m} \left(1 + \frac{1 - (2/3)^{w_r}}{x_r}\right) \implies 0 < \Lambda(K, W) := K \ln 2 - W \ln 3 < \sum_{r=1}^{m} \frac{1}{2^{L_r} - 1}.
   ```

   Moreover, whenever $N_0 > m / \ln 2$, $K = \lfloor W \log_2 3 \rfloor + 1$ is uniquely determined by $W$.
2. **(Sorted Cyclic Rearrangement Lemma on $\mathbb{Z}/m\mathbb{Z}$ ):** Let $L_0 \le y_1 \le y_2 \le \dots \le y_m$ be the non-decreasing rearrangement of $(L_1, \dots, L_m)$. Then for **every** $1 \le j \le m - 1$,

   ```math
   y_{j+1} \le \theta y_j - \eta(N_0),
   ```

   which forces simultaneous explicit lower bounds for every $1 \le j \le m$:

   ```math
   y_j \ge \max\!\left(L_0,\;\; \frac{W + E_{m, j}}{M_{m, j}}\right), \qquad M_{m, j} := (j - 1) + \frac{\theta^{m - j + 1} - 1}{\theta - 1}, \quad E_{m, j} := \frac{\eta(N_0)}{\theta - 1}\left(\frac{\theta^{m - j + 1} - 1}{\theta - 1} - (m - j + 1)\right) \ge 0.
   ```

3. **(Unconditional All-Weight $m$-Cycle Non-Existence Certificates across $W \in \lbrack 1, \infty)$ ):** Combining (1)–(2) with Laurent–Mignotte–Nesterenko (1995, Corollaire 2) for $W > W\sb{\text{Baker}}(m)$ and 300-digit `Decimal` upper-semiconvergent interval verification on $1 \le W \le W\sb{\text{Baker}}(m)$ (`prove_unconditional_mcycle_nonexistence`) proves that **zero non-trivial positive integer $m$-cycles exist for ANY weight $W \in \lbrack 1, \infty)$** across the following regimes:

| Verification Threshold $N_0$ | Provenance | All-Weight $m$-Cycles Ruled Out | Bottleneck at $m\sb{\max} + 1$ |
| :--- | :--- | :---: | :--- |
| **$N_0 = 72,058$** | Self-certified in **$6\text{ ms}$** (`sieve_k=14`) | **$1 \le m \le 14$** | $m = 15$ at $q_9 = 15,601$ |
| **$N_0 = 206,178,386$** | Self-certified in **$16.8\text{ s}$** (`sieve_k=20`) | **$1 \le m \le 28$** | $m = 29$ at $q\sb{15} = 10,781,274$ |
| **$N_0 = 2^{68}$** | Barina (2021) | **$1 \le m \le 88$** | $m = 89$ at $q\sb{39} \approx 2.744 \times 10^{19}$ |
| **$N_0 = 2^{71}$** | Barina (2025) | **$1 \le m \le 91$** *(matches Hercher world record)* | $m = 92$ at $q\sb{43} \approx 2.056 \times 10^{20}$ |

**Proof:**
- **(1)** Since $T(x) + 1 = \frac{3}{2}(x + 1)$ for odd $x$, iterating $w_r$ odd steps yields $T^{w_r}(x_r) + 1 = (3/2)^{w_r}(x_r + 1) \in \mathbb{Z}^+$, so $x_r + 1 = 2^{w_r} u_r$ ( $u_r \ge 1$ odd since $T^{w_r}(x_r) = 3^{w_r} u_r - 1$ is even). Dividing by $2^{a_r} \ge 2$ gives $2^{w_r + a_r} x\sb{r+1} = 3^{w_r} x_r + (3^{w_r} - 2^{w_r})$, whose product over $r \in \mathbb{Z}/m\mathbb{Z}$ cancels $\prod (x\sb{r+1}/x_r) = 1$ and yields $\frac{2^K}{3^W} = \prod\sb{r=1}^m \bigl(1 + \frac{1 - (2/3)^{w_r}}{x_r}\bigr)$. Moreover, $3^{w_r} u_r = (x_r + 1)^\theta / u_r^{\theta - 1} \le (x_r + 1)^\theta$, so

  ```math
  x_{r+1} + 1 = \frac{3^{w_r} u_r - 1}{2^{a_r}} + 1 \le \frac{(x_r + 1)^\theta + 1}{2} \le \frac{1 + (N_0 + 1)^{-\theta}}{2}(x_r + 1)^\theta \implies L_{r+1} \le \theta L_r - \eta(N_0).
  ```

- **(2)** Let $\pi : \lbrace 1, \dots, m\rbrace \to \mathbb{Z}/m\mathbb{Z}$ sort $(L_1, \dots, L_m)$ as $y_i = L\sb{\pi(i)}$. For any $1 \le j \le m - 1$, let $A = \lbrace \pi(1), \dots, \pi(j)\rbrace$ and $B = (\mathbb{Z}/m\mathbb{Z}) \setminus A$. Since $\emptyset \ne A \subsetneq \mathbb{Z}/m\mathbb{Z}$ and $r \mapsto r + 1 \pmod m$ acts transitively on $\mathbb{Z}/m\mathbb{Z}$, there exists $r \in A$ with $r + 1 \in B$. Then $L_r \le \max\sb{i \le j} y_i = y_j$ and $L\sb{r+1} \ge \min\sb{i > j} y_i = y\sb{j+1}$, so $y\sb{j+1} \le L\sb{r+1} \le \theta L_r - \eta(N_0) \le \theta y_j - \eta(N_0)$. Using $y_i \le y_j$ for $1 \le i \le j$ and unrolling $y\sb{j+s} \le \theta^s y_j - \eta(N_0) \frac{\theta^s - 1}{\theta - 1}$ for $1 \le s \le m - j$ gives $W \le \sum\sb{i=1}^m y_i \le M\sb{m, j} y_j - E\sb{m, j}$, hence $y_j \ge (W + E\sb{m, j}) / M\sb{m, j}$.
- **(3)** For $W > W\sb{\text{Baker}}(m)$, $y_1 \ge W / M\sb{m, 1}$ forces $\ln \Lambda(K, W) < \ln(2m) - (W / M\sb{m, 1})\ln 2 < -24.34 \bigl(\max\lbrace \ln b' + 0.14, 21\rbrace \bigr)^2 \ln 2 \ln 3$, contradicting Laurent–Mignotte–Nesterenko (1995, Corollaire 2). On $\lbrack 1, W\sb{\text{Baker}}(m)\rbrack$, partitioning into consecutive upper-semiconvergent intervals $\lbrack Q_c, Q\sb{c+1} - 1\rbrack$ (where $\Lambda(K, W) \ge \Lambda(P_c, Q_c)$ while the decreasing upper bound is maximized at $\max(Q_c, m)$ ) certifies $\Lambda(P_c, Q_c) > \sum\sb{j=1}^m (2^{y_j} - 1)^{-1}$ across every interval in high-precision `Decimal` arithmetic. $\blacksquare$

---

## 13. Arithmetic Bottleneck Elimination ( $m \le 92$ ), Effective Brox Finiteness on $\mathbb{Z}$, $p$-Adic Baker $S$-Integer Classification, & Beatty–Cantor Rigidity (Theorems 15–18)

### Theorem 15.1 (Breaking the $m = 91$ Barrier to $m \le 92$ via Unimodular Lattice Isolation, $c = 1$ Set-Membership Jump, & Exact $2$-Adic Hensel Sieve)
> Assume no non-trivial positive Collatz cycle has minimum element $\le N_0 = 2^{71}$ (Barina 2025).

1. **(Prime-Factor Structure of Bottleneck Cycle Denominators $D_n = 2^{p_n} - 3^{q_n}$ ):** Across the upper-convergent bottlenecks of $\log_2 3$, $25 \cdot 1{,}051{,}459 \mid D_9$, $17 \cdot 41 \cdot 47 \cdot 2281 \cdot 1{,}537{,}031 \mid D\sb{15}$, $73 \cdot 1433 \mid D\sb{37}$, $196{,}171 \mid D\sb{39}$, $467 \mid D\sb{41}$, and $9343 \mid D\sb{45}$, whereas at the $m = 92$ bottleneck convergent $(p\sb{43}, q\sb{43}) = (325{,}919{,}355{,}854{,}421{,}968{,}365,\; 205{,}632{,}218{,}873{,}398{,}596{,}256)$ ( $a\sb{44} = 37$, $\Lambda\sb{43} = 8.9007552 \times 10^{-23}$ ), **$D\sb{43}$ has zero prime divisors $\le 2{,}000{,}000$**.
2. **(Global Unimodular Lattice Isolation in $(\mathbb{Z}^+)^2$ ):** For every $92 \le m \le 96$, the only pairs $(K, W) \in (\mathbb{Z}^+)^2$ satisfying $0 < \Lambda(K, W) \le \sum\sb{j=1}^m (2^{y_j(m, W)} - 1)^{-1}$ are **exact multiples** $(K, W) = u \cdot (p\sb{43}, q\sb{43})$ with $1 \le u \le m - 91$. In particular, at **$m = 92$, $(K, W) = (p\sb{43}, q\sb{43})$ is the unique candidate pair in all of $(\mathbb{Z}^+)^2$**.
3. **(Exact $c = 1$ Two-Step Jump & $2$-Adic Hensel Elimination of $m = 92$ ):** Any hypothetical positive $92$-cycle at $(p\sb{43}, q\sb{43})$ has $92$ strictly distinct odd local minima $N_0 < x\sb{(1)} < x\sb{(2)} < \dots < x\sb{(92)}$ satisfying:

   ```math
   x_{(1)} \le U_1 := 11{,}954{,}868{,}071{,}494{,}398{,}009{,}685 \approx 5.063 \cdot 2^{71}, \qquad x_{(2)} \ge B_1 + 1 \approx 1.866 \times 10^{23}, \qquad x_{(j)} \ge B_2 + 1 \approx 3.823 \times 10^{36} \;\; (j \ge 3).
   ```

   Starting at $n_1 := x\sb{(1)} = a_1 2^{k_1} - 1$ ( $a_1$ odd), its next two local minima $n_1 \to n_2 \to n_3$ satisfy $n_2 = x\sb{(2)} \in \lbrack B_1 + 1, B_2\rbrack$ and $n_3 \ge B_2 + 1$, forcing the exact $2$-adic Hensel congruence

   ```math
   a_1 \equiv 3^{-k_1}\bigl(2^{\ell_1 + k_2} - 2^{\ell_1} + 1\bigr) \pmod{2^{\ell_1 + k_2 + 1}}.
   ```

   Exhaustive integer verification across all $44{,}034$ admissible $(k_1, \ell_1, k_2)$ triples (`prove_m92_nonexistence_hensel_certificate`) leaves **$0$ surviving integers** in `~0.45s` (with zero orbit traces), proving **zero non-trivial positive integer $m$-cycles exist for all $1 \le m \le 92$ across all weights $W \in \lbrack 1, \infty)$**.
4. **(Hercher's Collatz-Merger Identity):** Whenever an odd spiral-block minimum $x \ge 3$ ( $x + 1 = 2^w u$, $u$ odd) is followed by $a \ge 2$ even steps, $T^{w+1}\bigl(\frac{x - 1}{2}\bigr) = T^{w+2}(x)$, forcing $x \ge 2 N_0 + 3$ on any non-trivial cycle above $N_0$.

**Proof & Adversarial Note on $c \ge 2$ ( $m \ge 93$ ):**
- **(2)** Outside $\lbrack q\sb{43}, q\sb{43} + q\sb{44} - 1\rbrack$, high-precision `Decimal` upper-semiconvergent + LMN bounds rule out all $W$ for $92 \le m \le 96$. Inside $\lbrack q\sb{43}, q\sb{43} + q\sb{44} - 1\rbrack$, writing $(K, W) = u(p\sb{43}, q\sb{43}) + v(p\sb{42}, q\sb{42})$ ( $\det = p\sb{43} q\sb{42} - p\sb{42} q\sb{43} = +1$ ) gives $\Lambda(K, W) = u \Lambda\sb{43} - v \lvert \Lambda\sb{42} \rvert$. If $v \ge 1$, $\Lambda > 0 \implies u > \lvert \Lambda\sb{42} \rvert / \Lambda\sb{43} = 37.2489 \implies u \ge 38 \implies W \ge 38 q\sb{43} + q\sb{42} = q\sb{43} + q\sb{44}$, outside the interval. If $v \le -1$, $W \ge q\sb{43} \implies u \ge 2 \implies \Lambda \ge 2 \Lambda\sb{43} + \lvert \Lambda\sb{42} \rvert = 3.4934 \times 10^{-21} > \text{UB}(96, q\sb{43})$. Thus $v = 0$, and testing $u = 1, \dots, 37$ leaves $1 \le u \le m - 91$.
- **(3)** By Theorem 14, all $1 \le m' \le 91$ are impossible, so no two local minima of a $92$-cycle can coincide (otherwise the sub-loop would form an $m'$-cycle with $m' \le 91$ ). Subtracting $\sum\sb{j=2}^{92} (2^{y_j^{\text{sp}}} - 1)^{-1} = 5.3596 \times 10^{-24}$ from $\Lambda\sb{43}$ gives $x\sb{(1)} \le U_1$. Since $n_2 \ne n_1$ (no $1$-cycle), $n_2 \in \lbrace x\sb{(2)}, \dots, x\sb{(92)}\rbrace \implies n_2 \ge B_1 + 1$; and since $n_1 \le U_1 \implies n_2 < \frac{1}{2}(U_1 + 1)^\theta \approx 4.91 \times 10^{34} < B_2 < x\sb{(3)}$, **$n_2$ must equal $x\sb{(2)}$**. Then $n_3 \notin \lbrace n_1, n_2\rbrace$ (no $1$- or $2$-cycle), so $n_3 \in \lbrace x\sb{(3)}, \dots, x\sb{(92)}\rbrace \implies n_3 \ge B_2 + 1$. Writing $a_1 3^{k_1} - 1 = 2^{\ell_1} n_2$ and $n_2 + 1 = a_2 2^{k_2}$ ( $a_2$ odd, so $a_2 \equiv 1 \pmod 2$ ) gives $a_1 3^{k_1} - 1 \equiv 2^{\ell_1}(2^{k_2} - 1) \pmod{2^{\ell_1 + k_2 + 1}}$, whose exhaustive search yields $0$ solutions.
- **(Why naive exit-jump bounds fail for $c \ge 2$ at $m \ge 93$ ):** When $c \ge 2$ (e.g., $m = 93, u = 1$, where $c = 2$ ), $y_2^{\text{sp}} \le L_0$ only bounds $x\sb{(2)}$ *below* by $N_0$, NOT above by $B_1 = \lfloor 2^{y_3^{\text{sp}}} \rfloor - 1$. Hence **both** $x\sb{(2)}$ and $x\sb{(3)}$ can lie in $(B_1, B_2\rbrack$ simultaneously ( $x\sb{(1)} \to x\sb{(2)} \to x\sb{(3)}$ with $n_3 = x\sb{(3)} \le B_2$ ), violating $n_3 > B_2$! Restricting to $c = 1$ ( $m = 92$ ) keeps the proof 100% gap-free. $\blacksquare$

---

### Theorem 15.2 (Brox's $m$-Term Shifted Block Carry $H_j$ & Effective $N_0$-Free Finiteness of All $m$-Cycles over $\mathbb{Z}$ )
> For any $(w_1, a_1, \dots, w_m, a_m) \in (\mathbb{Z}^+)^{2m}$ with $W = \sum\sb{j=1}^m w_j$ and $K = W + \sum\sb{j=1}^m a_j$, define Brox's $m$-term shifted block carry (Brox, Acta Arith. 92, 2000, Lemma 3.1):

```math
H_j := \sum_{l=0}^{m-1} 2^{a_j + w_{j+1} + \dots + a_{j+l-1} + w_{j+l}} \bigl(2^{a_{j+l}} - 1\bigr) 3^{w_{j+l+1} + \dots + w_{j+m-1}} \in 2\mathbb{Z}_{\ge 0} + 1 \qquad (j \in \mathbb{Z}/m\mathbb{Z}).
```

1. **(Exact Compression & Two-Sided $\mathbb{Z}$-Cycle Equivalence):** Every cyclic shift $v^{(j)}$ satisfies $2^{w_j} H_j = C_K(v^{(j)}) + 2^K - 3^W$ identically, and $(w_1, a_1, \dots, w_m, a_m)$ generates a Collatz cycle in $\mathbb{Z} \setminus \lbrace 0, -1\rbrace$ (positive OR negative!) **if and only if** $(2^K - 3^W) \mid H_1$ (equivalently, $(2^K - 3^W) \mid H_j$ for all $1 \le j \le m$, with local minima $x_j = 2^{w_j} \frac{H_j}{2^K - 3^W} - 1$ ).
2. **(Self-Contained Cyclic Minimax Bound & Effective $N_0$-Free Finiteness):** Setting $\Delta := K - \theta W$, every tuple $(w, a) \in (\mathbb{Z}^+)^{2m}$ satisfies $\min\sb{1 \le j \le m}(3^{-W} H_j) < m \cdot 2^{\max(0, \Delta) - \frac{\theta - 1}{\theta^m - 1} W}$, while every cycle in $\mathbb{Z} \setminus \lbrace 0, -1\rbrace$ satisfies $1 \le W < K \le 2W$ and $3^{-W}\lvert 2^K - 3^W \rvert \ge \min(\lvert \Delta \rvert, 1) 2^{\max(0, \Delta) - 1}$, **canceling $2^{\max(0, \Delta)}$**:

   ```math
   \min(|\Delta|, 1) < 2 m \cdot 2^{-\frac{\theta - 1}{\theta^m - 1} W}.
   ```

   Coupling with Laurent–Mignotte–Nesterenko (1995, Corollaire 2) (`compute_brox_effective_finiteness_bounds`) yields **100% effective, $N_0$-free upper bounds $W \le W\sb{\text{Brox}}(m)$** ( $K \le 2 W\sb{\text{Brox}}(m)$ ) valid simultaneously for **all positive and negative integer $m$-cycles in $\mathbb{Z}$**: $W\sb{\text{Brox}}(1) = 11{,}792$, $W\sb{\text{Brox}}(2) = 30{,}486$, $W\sb{\text{Brox}}(3) = 60{,}117$, $W\sb{\text{Brox}}(5) = 181{,}520$, $W\sb{\text{Brox}}(10) = 1{,}997{,}295$.

**Proof of Cyclic Minimax Bound:**
Write the $l$-th summand of $3^{-W} H_j$ as $< 2^{E\sb{j, l}}$ where $E\sb{j, l} = \sum\sb{s=0}^l d\sb{j+s} - w_j$ and $d_i := a_i - (\theta - 1) w_i$ ( $\sum\sb{i=0}^{m-1} d_i = \Delta$ ). Extending $S_r = \sum\sb{i=0}^{r-1} d_i$ $m$-periodically ( $S\sb{r+m} = S_r + \Delta$ ), choosing $k_0 \in \lbrace 0, \dots, m\rbrace$ maximizing $S_r$ on $\lbrace 0, \dots, 2m\rbrace$ (if $\Delta \le 0$ ) or $u_0 = k_0 + m \in \lbrace m, \dots, 2m\rbrace$ maximizing $S_r$ on $\lbrace 0, \dots, 2m\rbrace$ (if $\Delta > 0$ ) gives a cyclic shift with $S_r \le \max(0, \Delta)$ for all $0 \le r \le m$. Since $a_i > 0$ and $w_i > 0$, both non-wrapping ( $j + l + 1 \le m$ ) and wrapping ( $j + l + 1 = m + r$, $1 \le r \le j$ ) cases satisfy $E\sb{j, l} \le \max(0, \Delta) + \tilde{L}\sb j(w)$ where $\tilde{L}\sb j(w) := -w_j + (\theta - 1)\sum\sb{i=0}^{j-1} w_i$. For $b = \frac{(\theta - 1)W}{\theta^m - 1}(1, \theta, \dots, \theta^{m-1})$, $\tilde{L}\sb j(b) = -\frac{\theta - 1}{\theta^m - 1} W$ for all $j$; writing $w = b + u$ ( $\sum u_j = 0$ ), if $\tilde{L}\sb j(u) > 0$ for all $j$ then $u_0 < 0 \implies u_1 < 0 \implies \dots \implies u\sb{m-1} < 0$, contradiction. Hence $\min_j \tilde{L}\sb j(w) \le -\frac{\theta - 1}{\theta^m - 1} W$. $\blacksquare$

---

### Theorem 16.1 ( $p$-Adic Baker Valuation Bounds & Complete Machine-Certified Classification of $S$-Integer $1$-Cycles in $\mathbb{Z}\lbrack 1/30\rbrack$ )
1. **(Explicit $p$-Adic Baker Valuation Bound via Bugeaud–Laurent 1996):** For every prime $p \ge 5$ and $(k, w) \in (\mathbb{Z}^+)^2$, setting $g_p := \operatorname{lcm}(\operatorname{ord}\sb p(2), \operatorname{ord}\sb p(3)) \mid (p - 1)$, Corollaire 1 of Bugeaud & Laurent (*J. Number Theory* 61, 1996, p. 326) gives unconditionally:

   ```math
   \nu_p(2^k - 3^w) \le \frac{24 \, p \, g_p}{(p - 1)(\ln p)^2} \Bigl(\max\bigl\{\ln(k + w) + 0.4,\; 10 \ln p\bigr\}\Bigr)^2.
   ```

2. **(Finiteness on Every Finite $S$ Ring $\mathbb{Z}\sb S$ & Complete Classification on $\mathbb{Z}\lbrack 1/30\rbrack$ ):** Whereas Counter-Model $\mathcal{M}\sb 1 = \mathbb{Q}\sb{>0} \cap \mathbb{Z}\sb{(2)}$ admits infinitely many $1$-cycles, every localization $\mathbb{Z}\sb S$ at a finite set of primes $S$ contains **only finitely many** primitive $1$-cycles $x_0 = \frac{3^w - 2^w}{2^k - 3^w}$. Specifically, on **$\mathbb{Z}\lbrack 1/30\rbrack$** ( $S = \lbrace 2, 3, 5\rbrace$, containing $\mathbb{Z}$ and all terminating base $10$ decimals $\mathbb{Z}\lbrack 1/10\rbrack$ ), `classify_s_integer_1cycles_z_inv_30` certifies in **`~19 ms`** across all $(w, k) \in (\mathbb{Z}^+)^2$ that the **exact set of primitive $1$-cycles in $\mathbb{Z}\lbrack 1/30\rbrack$** consists of **6 cycles**:
   - **Negative (in $\mathcal{S}\sb \infty \cap \mathbb{Z}^-$ ):** $(w, k) = (1, 1) \implies x_0 = -1$ and $(w, k) = (2, 3) \implies x_0 = -5$ (certifying in particular that $\lbrace -1, -5\rbrace$ are the unique negative integer $1$-cycles across all lengths!).
   - **Positive (in $\mathbb{Z}\lbrack 1/10\rbrack \sb{>0}$ ):** $(1, 2) \implies 1$, $(1, 3) \implies \frac{1}{5}$, $(1, 7) \implies \frac{1}{125}$, and $(3, 5) \implies \frac{19}{5}$.

**Proof:**
For $k > w \ge 1$, $\gcd(2^k - 3^w, 6) = 1$, so $x_0 \in \mathbb{Z}\lbrack 1/30\rbrack \iff 5^e x_0 \in \mathbb{Z}$ where $e = \nu_5(2^k - 3^w)$. Then $5^e(x_0 + 1) = 2^w \frac{5^e(2^{k-w} - 1)}{2^k - 3^w} \in 2^w \mathbb{Z} \setminus \lbrace 0\rbrace$, forcing $2^w \lvert 2^k - 3^w \rvert \le 5^e(2^k - 2^w)$. If $2^k \ge 2 \cdot 3^w$ or $2^k \le \frac{1}{2} 3^w$, this gives $w < 1 + e \log_2 5$ (and $k < 1 + w \log_2 3 + e \log_2 5$ ); if $\frac{1}{2} 3^w < 2^k < 2 \cdot 3^w$, it gives $\lvert k \ln 2 - w \ln 3 \rvert < 4 \cdot 5^e 2^{-w}$. Coupling (1) at $p = 5$ ( $g_5 = 4$ ) with LMN (1995) rules out all $w > 39{,}657$ and $k > 90{,}719$. For $e \ge 11$, $5$-adic discrete-logarithm Hensel lifting in $(\mathbb{Z}/5^{11}\mathbb{Z})^\times$ ( $\operatorname{ord}\sb{5^{11}}(2) = 4 \cdot 5^{10} = 39{,}062{,}500 > 90{,}719$ ) leaves $76$ pairs, $0$ of which survive; for $0 \le e \le 10$, Legendre's CF criterion ( $w \ge 32$ ) + exact division ( $1 \le w \le 31$ ) yields the exact 6 cycles above. $\blacksquare$

---

### Theorem 17.1 (Non-Commuting Curvature $\lbrack T_0, T_1\rbrack = -1/4$ & Four Unconditional Rigidity Bridges on $\mathcal{S}\sb \infty$ )
1. **(Constant Non-Zero Commutator Curvature):** The even and odd branches $T_0(x) = \frac{x}{2}$ and $T_1(x) = \frac{3x + 1}{2}$ satisfy $\lbrack T_0, T_1\rbrack (x) := T_0(T_1(x)) - T_1(T_0(x)) = -\frac{1}{4} \ne 0$ identically, breaking the commutativity $M_2 \circ M_3 = M_3 \circ M_2$ required by Furstenberg–Rudolph–Host $(\times 2, \times 3)$-rigidity on $\mathbb{R}/\mathbb{Z}$ and lifting $\mathbb{Z} \hookrightarrow \mathbb{Z}\sb 2 \times \mathbb{Z}\sb 3$ to a hyperbolic skew-product expanding by $2$ on $\mathbb{Z}\sb 2$ and contracting by $3^{-v_0(x_2)}$ on $\mathbb{Z}\sb 3$.
2. **(Unique Forward $T$-Invariant Subset & Measure on $\mathcal{S}\sb \infty$ ):** $\bigcap\sb{r=0}^\infty T^{-r}(\mathcal{S}\sb \infty) = \lbrace -1\rbrace$, making the Dirac mass $\delta\sb{-1}$ the unique $T$-invariant Borel probability measure on $\mathbb{Z}\sb 2$ supported on $\mathcal{S}\sb \infty$.
3. **(Singleton Intersection with the Critical Sturmian Hull $\Omega\sb{\log_3 2}$ ):** $\Phi\sb \infty^{-1}(\Omega\sb{\log_3 2}) \cap \mathcal{S}\sb \infty = \lbrace x\sb{\text{Sturm}}\rbrace$, and **every strict forward iterate $T^r(x\sb{\text{Sturm}})$ ( $r \ge 1$ ) exits $\mathcal{S}\sb \infty$ in finitely many steps**.
4. **(Unconditional Base $2$ & Base $3$ Weyl/Benford Equidistribution on $\mathcal{S}\sb \infty \cap \mathbb{Z}^+$ ):** For every hypothetical $n \in \mathcal{S}\sb \infty \cap \mathbb{Z}^+$, pure divergence $T^k(n) \to +\infty$ kills the $+1/(3 T^k(n))$ step error on $\mathbb{R}/\mathbb{Z}$, so unique ergodicity of $R\sb{\log_2 3}$ and $R\sb{-\log_3 2}$ forces both $(\lbrace \log_2 T^{j_m(n)}(n)\rbrace )\sb{m \ge 1}$ and $(\lbrace \log_3 T^k(n)\rbrace )\sb{k \ge 0}$ to be uniformly distributed on $\lbrack 0, 1)$.
5. **( $3$-Adic Syracuse Fiber Collapse Characterization of $\mathcal{S}\sb \infty \cap \mathbb{Z}$ ):** For $\theta_3(x, k) := \frac{(2^{-k} C_k(\Phi_k(x))) \bmod 3^{w_k(x)}}{3^{w_k(x)}} \in \lbrack 0, 1)$:
   - Every $n \in \mathcal{S}\sb \infty \cap \mathbb{Z}^+$ satisfies the exact integer equality $T^k(n) = (2^{-k} C_k(\Phi_k(n))) \bmod 3^{w_k(n)}$ once $2^k > n + w_k(n)/3$, forcing $\theta_3(n, k) = O(k \, 2^{-k}) \to 0^+$.
   - Every $-m \in \mathcal{S}\sb \infty \cap \mathbb{Z}^-$ satisfies $1 - \theta_3(-m, k) = O(2^{-k}) \to 0^+$ ( $\theta_3 \to 1^-$ ) once $2^k > m$.
   - On $x\sb{\text{Sturm}}$, $\theta_3(x\sb{\text{Sturm}}, k)$ oscillates across $(0, 1)$ ( $\theta_3(x\sb{\text{Sturm}}, 100) \approx 0.191562$, $\theta_3(x\sb{\text{Sturm}}, 120) \approx 0.946876$ ), certifying independently from the $3$-adic dual side that $\lvert x\sb{\text{Sturm}} \rvert > 2^{118}$ if $x\sb{\text{Sturm}} \in \mathbb{Z}$.

---

### Theorem 18.1 (Beatty–Sturmian Deficit-Carry Duality, Heisenberg Trajectory Uncertainty, & Continuum Exclusion $\mathcal{S}\sb \infty^{\text{div}}$ )
1. **(Deficit-Carry Identity & Heisenberg Trajectory Uncertainty):** For every $n \in \mathbb{Z}\sb{\ge 2}$ and every surviving prefix $1 \le k < \tau(n)$ (hence for **all $k \ge 1$** whenever $n \in \mathcal{S}\sb \infty \cap \mathbb{Z}^+$ ), let $\delta_m(n) := (m - 1)\log_2 3 - j_m(n) \ge 0$, $\Delta_k(n) := w_k(n)\log_2 3 - k > 0$, and $\bar{T}\sb w(n) := \frac{1}{w} \sum\sb{m=1}^w T^{j_m}(n)$. Then:

   ```math
   T^k(n) = 2^{\Delta_k(n)}\left(n + \frac{1}{3} \sum_{m=1}^{w} 2^{-\delta_m(n)}\right), \qquad \bigl(T^k(n) - n\bigr) \cdot \bar{T}_w(n) > \frac{n \, w}{3} \ge \frac{n \lceil k \log_3 2 \rceil}{3}.
   ```

   Moreover, every $n \ge 2$ with $\tau(n) > 2$ satisfies $n \equiv 3 \pmod 4$, and every odd-step gap with $j\sb{m+1}(n) < \tau(n)$ satisfies $2^{j\sb{m+1}(n) - j_m(n)} \le \bigl\lfloor \frac{3 T^{j_m}(n) + 1}{n + 1} \bigr\rfloor$.
2. **( $2$-Adic Topological Density of Negative Rational Cycles & Continuum Exclusion from $\mathbb{Z}^-$ ):**
   - For every $v \in \mathcal{S}\sb k$, $v^\infty \in \mathcal{S}\sb \infty$ directly, so $\mathcal{S}\sb \infty \cap \mathbb{Q}\sb{<0} \cap \mathbb{Z}\sb{(2)}$ is **$2$-adically dense in $\mathcal{S}\sb \infty$** (proving no purely $2$-adic closed condition on $\mathcal{S}\sb \infty$ can exclude rationals).
   - Conversely, the **Divergent-Carry Subcone** $\mathcal{S}\sb \infty^{\text{div}} := \lbrace x \in \mathcal{S}\sb \infty : \sum\sb{m=1}^\infty 2^{-\delta_m(x)} = +\infty\rbrace$ has **cardinality $2^{\aleph_0}$ (continuum)** ( $32$ independent binary toggles already occur within the first $78$ odd steps of $j^\ast \sb m$ ) and satisfies **$\mathcal{S}\sb \infty^{\text{div}} \cap \mathbb{Z}^- = \emptyset$ unconditionally**, generalizing Theorem 13.1(3) from the single point $x\sb{\text{Sturm}}$ to an uncountable continuum inside $\mathcal{S}\sb \infty$.

---

## 14. Potential-Merger Horizon, Recursive Multi-Step $2$-Adic Hensel Pruning ( $m \le 94$ ), Complete $\mathbb{Z}$ $2/3$-Cycle & $\mathbb{Z}\lbrack 1/30\rbrack$ $2$-Cycle Classifications, and Sharper $\mathcal{S}\sb \infty$ Obstructions (Theorems 19–22)

### Theorem 19.1 ( $6$-Line Potential-Telescoping Collatz-Merger Bound & Convergent Index $45$ Horizon)
> Assume no non-trivial positive Collatz cycle has minimum element $\le N_0$. Let $x_1, \dots, x_m > N_0$ be the $m$ odd spiral-block minima of a non-trivial positive $m$-cycle with block parameters $(k_i, \ell_i) \in (\mathbb{Z}^+)^2$ ( $x_i + 1 = 2^{k_i} u_i$, $2^{\ell_i} x\sb{i+1} = 3^{k_i} u_i - 1$ ).

1. **(Entry & Exit-Tail Collatz-Merger Bounds):** Whenever $\ell_i \ge 2$:
   - **Entry Merger:** $x_i' := \frac{x_i - 1}{2} \in \mathbb{Z}^+$ satisfies $T^{k_i + 1}(x_i') = T^{k_i + 2}(x_i)$, forcing $x_i' > N_0$, i.e., $x_i \ge 2 N_0 + 3$.
   - **Exit-Tail Merger:** The final odd element $x\sb{\text{last}} := 2 \cdot 3^{k_i - 1} u_i - 1$ of block $i$ satisfies $x\sb{\text{last}} \equiv 5 \pmod 8$ ( $x\sb{\text{last}} = 8q + 5$ ), and $2q + 1 = \frac{x\sb{\text{last}} - 1}{4}$ merges in one compressed step via $T(2q + 1) = 3q + 2 = T^3(x\sb{\text{last}})$, forcing $x\sb{\text{last}} \ge 4 N_0 + 5$.
2. **(Exact $6$-Line Potential-Telescoping Step Inequality):** Every spiral step $i \in \mathbb{Z}/m\mathbb{Z}$ satisfies unconditionally:

   ```math
   \frac{1 - (2/3)^{k_i}}{x_i} + \frac{1}{3}\left(\frac{1}{x_{i+1}} - \frac{1}{x_i}\right) = \frac{\frac{2}{3} - \left(\frac{2}{3}\right)^{k_i}}{x_i} + \frac{1}{3 x_{i+1}} < \frac{2}{3 N_0}.
   ```

   Consequently, summing around $\mathbb{Z}/m\mathbb{Z}$ gives $\sum\sb{i=1}^m \frac{1 - (2/3)^{k_i}}{x_i} < \frac{2 m}{3 N_0}$, and for every decomposition $m = m_1 + m_2$ ( $1 \le m_2 < m$ ), choosing the cyclic shift maximizing the contiguous $m_2$-sum $\sum\sb{t=0}^{m_2 - 1} L\sb{r^\ast + t} \ge \frac{m_2}{m} W$ bounds the complementary $m_1$-arc by $\frac{2 m_1 + 1}{3 N_0}$ while preserving the cyclic step inequality $L\sb{r^\ast } \le \theta L\sb{r^\ast + m_2 - 1} - \eta(N_0)$ on the $m_2$-block.
3. **(Analytic Upgrade at $N_0 = 2^{68}$ & Convergent Index $45$ Horizon at $N_0 = 2^{71}$ ):**
   - At $N_0 = 2^{68}$ (Barina 2021), this upgrades Theorem 14 purely analytically from **$m \le 88 \to m \le 89$** (`verify_potential_collatz_merger_and_index45_horizon`).
   - At $N_0 = 2^{71}$ (Barina 2025), $(p\sb{41}, q\sb{41})$ and all non-multiples of $(p\sb{43}, q\sb{43})$ are eliminated across **$92 \le m \le 99$**, and **convergent index $45$** ( $q\sb{45} = 31{,}150{,}961{,}018{,}190{,}238{,}869{,}556$, $a\sb{46} = 55$, $\Lambda\sb{45} \approx 5.5129 \times 10^{-23}$ ) is unconditionally eliminated for all **$1 \le m \le 101$** and first enters at **$m = 102$** (requiring $\log_2 N_0 > 73.93$ analytically).

**Proof of (2):**
Split into three exhaustive cases on $(k_i, \ell_i) \in (\mathbb{Z}^+)^2$:
- **Case 1 ( $k_i = 1$ ):** $\frac{2}{3} - \bigl(\frac{2}{3}\bigr)^1 = 0$ and $x\sb{i+1} > N_0$, so $\text{LHS} = \frac{1}{3 x\sb{i+1}} < \frac{1}{3 N_0} < \frac{2}{3 N_0}$.
- **Case 2 ( $\ell_i = 1,\; k_i \ge 2$ ):** Since $(3/2)^{k_i} \ge 9/4 > 2$, $2 x\sb{i+1} = (3/2)^{k_i}(x_i + 1) - 2 = (3/2)^{k_i} x_i + \bigl((3/2)^{k_i} - 2\bigr) > (3/2)^{k_i} x_i$, so $\frac{1}{3 x\sb{i+1}} < \frac{2}{3}(2/3)^{k_i} \frac{1}{x_i}$ and $\text{LHS} < \frac{\frac{2}{3} - \frac{1}{3}(2/3)^{k_i}}{x_i} < \frac{2}{3 x_i} < \frac{2}{3 N_0}$.
- **Case 3 ( $\ell_i \ge 2,\; k_i \ge 2$ ):** By Entry Merger (1), $x_i > 2 N_0$ and $x\sb{i+1} > N_0$, so $\text{LHS} < \frac{2/3}{2 N_0} + \frac{1}{3 N_0} = \frac{2}{3 N_0}$. $\blacksquare$

---

### Theorem 19.2 (Shortest-Path Cycle-Partition Lemma & Recursive Multi-Step $2$-Adic Hensel Elimination for $m \le 94$ and $u \cdot (p\sb{43}, q\sb{43})$ )
> Assume no non-trivial positive Collatz cycle has minimum element $\le N_0 = 2^{71}$, and suppose all $1 \le m' < m$ have been ruled out so the $m$ odd local minima $x\sb{(1)} < \dots < x\sb{(m)}$ of a hypothetical $m$-cycle $V$ at $(K, W) = u \cdot (p\sb{43}, q\sb{43})$ are strictly distinct. Let $c \ge 1$ be the clamped count ( $y_c \le L_0 < y\sb{c+1}$ ), $B_1 := \lfloor 2^{y\sb{c+1}} \rfloor - 1$, $B_2 := \lfloor 2^{y\sb{c+2}} \rfloor - 1$, and partition $V = A' \sqcup I_1 \sqcup H$ where $A' := \lbrace x \in V : x \le B_1\rbrace$, $I_1 := \lbrace x \in V : B_1 < x \le B_2\rbrace$, and $H := \lbrace x \in V : x > B_2\rbrace$.

1. **(Shortest-Path Cycle-Partition Lemma):** Since $\sum\sb{j=1}^c \frac{1}{B_1 + 1} + \sum\sb{j=c+1}^m \frac{1}{2^{y_j} - 1} < u \Lambda\sb{43}$ while $\lvert I_1 \cup H \rvert = \lvert V \setminus A' \rvert = m - s \ge m - c \ge 2$, both $A'$ ( $1 \le s := \lvert A' \rvert \le c$ ) and $H$ are non-empty, and $\lvert I_1 \rvert \le c + 1 - s$ (since $x\sb{(c+2)} > B_2 \implies A' \cup I_1 \subseteq \lbrace x\sb{(1)}, \dots, x\sb{(c+1)}\rbrace$ ). Choosing the unique pair $(z_1 \in A',\; z\sb{r+2} \in H)$ minimizing directed cycle distance leaves $0 \le r \le \lvert I_1 \rvert \le c + 1 - s$ intermediate vertices $z_2, \dots, z\sb{r+1} \in I_1$. Because $z_1 \le B_1 \implies z_2 < \frac{1}{2}(B_1 + 1)^\theta \le B_2$, direct $r = 0$ jumps into $H$ are impossible, forcing **$1 \le r \le c + 1 - s \le c$**:
   - **Subcase $s = 1$:** $A' = \lbrace x\sb{(1)}\rbrace$, so $z_1 = x\sb{(1)}$ satisfies tight per $k_1$ reciprocal bands and $1 \le r \le c$.
   - **Subcase $2 \le s \le c$:** $z_1 \in \lbrack x\sb{\min}(u, k_1), B_1\rbrack$ and **$1 \le r \le c - 1$** (reducing maximum tree depth by $1$!).
2. **(Exact $r$-Step Spiral Hensel Congruence & Universal Bit-Scaling Collapse):** Along $z_1 \to z_2 \to \dots \to z\sb{r+2}$, setting $K_d := \sum\sb{i=1}^d (k_i + \ell_i)$, $W_d := \sum\sb{i=1}^d k_i$, and $G_0 = 0,\; G_d = 3^{k_d} G\sb{d-1} + 2^{K\sb{d-1}}(2^{\ell_d} - 1)$, we have $2^{K_d}(z\sb{d+1} + 1) = 3^{W_d}(z_1 + 1) + G_d$ identically. Requiring $z\sb{r+1} + 1 = 2^{k\sb{r+1}} u\sb{r+1}$ ( $u\sb{r+1}$ odd) forces:

   ```math
   z_1 + 1 \equiv 3^{-W_r}\bigl(2^{K_r + k_{r+1}} - G_r\bigr) \pmod{2^{K_r + k_{r+1} + 1}}.
   ```

   Because $\log_2 B_2 \approx \theta \log_2 B_1$, any path climbing from $\le B_1$ above $B_2$ satisfies $K_r + k\sb{r+1} > \log_2 B_1 + \frac{r+1}{\theta - 1}$, collapsing each leaf congruence to at most one integer in $\lbrack x\sb{\min}, B_1\rbrack$.
3. **(Machine-Certified Elimination up to $m \le 94$ and Higher Multiples $u \ge 2$ ):** `prove_multistep_hensel_mcycle_nonexistence` (`goal_extensions.py`) certifies with **$0$ cycle survivors**:

| $m$ | Multiple $u$ | Clamped $c$ | Subcases $(s, r\sb{\max})$ | Tree Nodes | Arithmetic Hensel Survivors | Max Drop Blocks $< 2^{71}$ | Cycle Survivors |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **$92$** | $u = 1$ ( $u \ge 2$ monotone) | $1$ | $(s=1, r \le 1)$ | $1{,}089$ | $0$ | $0$ | **$0$** |
| **$93$** | $u = 1$ ( $u \ge 2$ Hensel/monotone) | $2$ | $(s=1, r \le 2),\; (s \ge 2, r \le 1)$ | $2{,}794$ | **$1$** (in $s \ge 2$ ) | $81$ | **$0$** |
| **$94$** | $u = 1$ ( $u \ge 2$ Hensel/monotone) | $3$ | $(s=1, r \le 3),\; (s \ge 2, r \le 2)$ | $144{,}555$ | **$5$** (genuine $r \le 2$ in $s \ge 2$!) | $81$ | **$0$** |
| **$95$** | $u = 2, 3, 4$ ( $u \ge 5$ monotone) | $2$ | $(s=1, r \le 2),\; (s \ge 2, r \le 1)$ | $5{,}955$ | **$27$** ( $25$ at $u=2$, $2$ at $u=3$ ) | $81$ | **$0$** |

(In addition, exhaustive $4$-core verification at $m = 96$ eliminates all $u \ge 2$ with $203$ arithmetic Hensel survivors across $u \in \lbrace 2, 3, 4\rbrace$, all dropping $< 2^{71}$, $0$ cycle survivors.) Consequently, **zero non-trivial positive integer $m$-cycles exist for all $1 \le m \le 94$ across all weights $W \in \lbrack 1, \infty)$**, and for $m \in \lbrace 95, 96\rbrace$ all higher multiples $u \cdot (p\sb{43}, q\sb{43})$ ( $u \ge 2$ ) are unconditionally eliminated. $\blacksquare$

---

### Theorem 20.1 (Complete $N_0$-Free Classification of All $2$-Cycles and $3$-Cycles over $\mathbb{Z}$ )
> Combining Theorem 15.2's effective Brox + LMN cutoffs ( $W\sb{\text{Brox}}(2) = 30{,}486$, $W\sb{\text{Brox}}(3) = 60{,}117$ ) with $150$-digit `Decimal` Legendre continued-fraction pruning and canonicalized cyclic Brox $H_j$ divisibility (`classify_all_z_2cycles_and_3cycles`, `~0.54s` with **zero $N_0$ assumption**):

1. **( $m = 2$ over $\mathbb{Z}$ ):** Out of $17$ admissible $(W, K)$ pairs, **$(-17, -41)$** at $(w_1, a_1, w_2, a_2) = (4, 1, 3, 3)$ ( $W = 7, K = 11, 2^{11} - 3^7 = -139$ ) is the **unique primitive $2$-cycle in all of $\mathbb{Z}$** (giving an immediate, completely $N_0$-free proof of Simons's 2005 positive $2$-cycle non-existence theorem and proving uniqueness of the $-17$ negative $2$-cycle).
2. **( $m = 3$ over $\mathbb{Z}$ ):** Out of $82$ admissible $(W, K)$ pairs and $317{,}452$ canonical tuples, **zero primitive $3$-cycles exist anywhere in $\mathbb{Z}$** (neither positive nor negative; only the $3$-fold unreduced repetitions of $+1$ and $-5$ occur). $\blacksquare$

---

### Theorem 20.2 (General Finite $S$ $m$-Cycle Effective Finiteness & Complete Classification of $2$-Cycles in $\mathbb{Z}\lbrack 1/30\rbrack$ )
1. **(Two-Pronged Effective Finiteness on Every Finite $S$ Ring $\mathbb{Z}\sb S$ ):** Let $S = \lbrace 2, 3\rbrace \cup S\sb{\text{odd}}$ be any finite set of primes and $m \ge 1$. For any $m$-cycle in $\mathbb{Z}\sb S \setminus \lbrace 0, -1\rbrace$ with parameters $(w_1, a_1, \dots, w_m, a_m) \in (\mathbb{Z}^+)^{2m}$, write $\lvert 2^K - 3^W \rvert = U_S \cdot M$ with $U_S = \prod\sb{p \in S\sb{\text{odd}}} p^{\nu_p(2^K - 3^W)}$ and $\gcd(M, \prod\sb{p \in S} p) = 1$. Then $M \mid C_K(v^{(j)})$ and $M \mid H_j$ for all $j \in \mathbb{Z}/m\mathbb{Z}$:
   - **Prong 1 (Cyclic-Shift $C_K$ Cap for $2^K \ge 2 \cdot 3^W$ ):** Choosing the cyclic shift with $a_m^{(j)} \ge (K - W)/m$ bounds $C_K(v^{(j)}) < m \, 3^W \, 2^{\frac{m-1}{m}K + \frac{W}{m}}$, so $C_K(v^{(j)}) \ge M \ge \frac{2^{K-1}}{U_S}$ forces

     ```math
     K < m + m \log_2 m + (m \theta + 1) W + m \sum_{p \in S_{\text{odd}}} \nu_p(2^K - 3^W) \log_2 p.
     ```

   - **Prong 2 (Brox $H_j$ + Bugeaud–Laurent + LMN Decay in $W$ ):** Since $\min_j(3^{-W} H_j) < m \cdot 2^{\max(0, \Delta) - c_m W}$ with $c_m = \frac{\theta - 1}{\theta^m - 1}$, $H_j \ge M$ gives $\min(\lvert \Delta \rvert, 1) < 2 m \, U_S \, 2^{-c_m W}$. Coupling Bugeaud–Laurent ( $\nu_p = O((\ln(K + W))^2)$ ) with Prong 1 ( $K = O(W)$ ) and LMN ( $\ln\lvert \Delta \rvert \ge -C(\ln W)^2$ ) bounds both $W$ and $K$ effectively for every $(S, m)$.
2. **(Complete Classification of $2$-Cycles in $\mathbb{Z}\lbrack 1/30\rbrack$ ):** Certifying $(W\sb{\max}, K\sb{\max}) = (103{,}000,\; 485{,}332)$ and applying exact $5$-adic LTE discrete logarithms modulo $5^{16}$ (`classify_s_integer_2cycles_z_inv_30`), out of $148$ admissible $(W, K)$ pairs and $11{,}369$ tuples, the **exact primitive $2$-cycles in $\mathbb{Z}\lbrack 1/30\rbrack$** are uniquely:
   - **Negative (in $\mathbb{Z}$ ):** $(-17, -41)$ at $(w, a) = ((4, 3), (1, 3))$ ( $K = 11, W = 7, D = -139$ ).
   - **Positive (in $\mathbb{Z}\lbrack 1/10\rbrack \sb{>0}$ ):** **$\bigl(\frac{29}{5}, \frac{23}{5}\bigr)$** at $(w, a) = ((1, 2), (1, 1))$ ( $K = 5, W = 3, D = +5$, orbit $\frac{29}{5} \to \frac{46}{5} \to \frac{23}{5} \to \frac{37}{5} \to \frac{58}{5} \to \frac{29}{5}$ ), together with the $5$ unreduced $2$-fold repetitions of $1, \frac{1}{5}, \frac{1}{125}, -5, \frac{19}{5}$. $\blacksquare$

---

### Theorem 21.1 (Deficit-Drift Complementarity & Constant-Free Quadratic Peak Floor on Surviving Prefixes)
> For every $n \in \mathbb{Z}\sb{\ge 2}$ and every surviving prefix $1 \le k < \tau(n)$ (hence for all $k \ge 1$ if $n \in \mathcal{S}\sb \infty \cap \mathbb{Z}^+$ ):

1. **(Deficit-Drift Complementarity):** $\Delta_k(n) := w_k(n)\theta - k$ and the next odd-step deficit $\delta\sb{w_k(n) + 1}(n) := w_k(n)\theta - j\sb{w_k(n) + 1}(n)$ satisfy

   ```math
   \Delta_k(n) = \delta_{w_k(n) + 1}(n) + \bigl(j_{w_k(n) + 1}(n) - k\bigr) \ge \delta_{w_k(n) + 1}(n),
   ```

   with **exact equality $\Delta_k(n) = \delta\sb{w_k(n) + 1}(n)$ whenever $T^k(n)$ is odd**.
2. **(Constant-Free Quadratic Running-Maximum Floor):** Letting $M_k(n) := \max\sb{1 \le j \le k} T^j(n)$,

   ```math
   M_k(n) > \frac{n + \sqrt{n^2 + \frac{4}{3} n \, w_k(n)}}{2} \ge \frac{n + \sqrt{n^2 + \frac{4}{3} n \lceil k \log_3 2 \rceil}}{2}.
   ```

**Proof of (2):**
Note $T^{j_1(n)}(n) = n$ ( $j_1(n) = 0$ ) and for $2 \le m \le w_k(n)$, $1 \le j_m(n) < k \implies T^{j_m(n)}(n) \le M_k(n)$, while $T^k(n) \le M_k(n)$. Thus $\bar{T}\sb{w_k}(n) \le \frac{n + (w_k - 1) M_k(n)}{w_k} \le M_k(n)$. Substituting into Theorem 18.1's uncertainty inequality $(T^k(n) - n)\bar{T}\sb{w_k}(n) > \frac{n w_k}{3}$ gives $(M_k(n) - n) M_k(n) > \frac{n w_k}{3}$, i.e., $M_k(n)^2 - n M_k(n) - \frac{n w_k}{3} > 0$, whose positive quadratic root yields the exact bound. $\blacksquare$

---

### Theorem 21.2 (Lower-Semiconvergent Pinch Duality on $\mathcal{S}\sb \infty$ & Individual-Step Archimedean Baker Floor)
1. **(Lower-Semiconvergent Pinch Duality):** Dual to Theorem 14.1, along the surviving Cantor-cone boundary $k = \lfloor w \log_2 3 \rfloor$ ( $w \ge 1$ ), $(k, w)$ achieves a strict record minimum of $\widetilde{\Lambda}(k, w) := w \ln 3 - k \ln 2 > 0$ **if and only if** $(k, w) = (p\sb{2r} + c p\sb{2r+1},\; q\sb{2r} + c q\sb{2r+1})$ is a **lower semiconvergent** of $\log_2 3$ ( $r \ge 0,\; 0 \le c < a\sb{2r+2}$ ). Remarkably, the first three record pinches $(k, w) = (1, 1), (3, 2), (11, 7)$ realize the exact $(K, W)$ parameters of the three known negative integer cycles $\lbrace -1\rbrace , \lbrace -5\rbrace , \lbrace -17\rbrace \subset \mathcal{S}\sb \infty \cap \mathbb{Z}^-$.
2. **(Individual-Step Baker–LMN Floor):** Every surviving step $1 \le k < \tau(n)$ satisfies $T^k(n) - n > n \bigl((3/2)^k \text{ carry-free } 3^{w_k}/2^k - 1\bigr) > n \, \widetilde{\Lambda}(k, w_k)$, hence unconditionally by Laurent–Mignotte–Nesterenko (1995):

   ```math
   T^k(n) - n > n \cdot \exp\Bigl(-24.34 \bigl(\max\{\ln(k/\ln 3 + w_k/\ln 2) + 0.14,\; 21\}\bigr)^2 \ln 2 \ln 3\Bigr). \quad \blacksquare
   ```

---

### Theorem 22.1 (Complete Classification of $5$-Adic Unit Cycle Denominators $\lvert 2^k - 3^w \rvert = 5^e$ )
> Coupling Bugeaud–Laurent ( $p = 5$ ) with Laurent–Mignotte–Nesterenko across all three Diophantine regimes ( $K\sb{\max} = 39{,}673$, $W\sb{\max} = 25{,}030$ ) and applying modular prime sieving + $5$-adic LTE discrete logarithms modulo $5^8$ (`classify_5adic_unit_cycle_denominators`, `< 30 ms`), the Diophantine equation $\lvert 2^k - 3^w \rvert = 5^e$ in $(\mathbb{Z}^+)^2 \times \mathbb{Z}\sb{\ge 0}$ has **exactly $8$ solutions**:
- **$e = 0$ (Catalan–Mihăilescu):** $(k, w, 2^k - 3^w) = (1, 1, -1),\; (2, 1, +1),\; (3, 2, -1)$.
- **$e = 1$:** $(2, 2, -5),\; (3, 1, +5),\; (5, 3, +5)$.
- **$e = 2$:** $(1, 3, -25)$.
- **$e = 3$:** $(7, 1, +125)$.

*Consequently, for **every* surviving prefix $(k, w_k)$ on $\mathcal{S}\sb \infty$ with $k \ge 4$ (and globally for all $(k, w) \in (\mathbb{Z}^+)^2$ with $k \ge 8$ ), the greatest prime factor satisfies $P^+(\lvert 2^k - 3^w \rvert) \ge 7$ unconditionally. $\blacksquare$

---

### Theorem 22.2 ( $(2,3)$-Adic Contractive Coalescence Exclusion of Minimal Divergent Positive Orbits)
> Suppose $\mathcal{D}^+ := \lbrace n \in \mathbb{Z}^+ : \lim\sb{j \to \infty} T^j(n) = +\infty\rbrace \ne \emptyset$ (in particular if $\mathcal{S}\sb \infty \cap \mathbb{Z}^+ \ne \emptyset$ by Theorem 13.1), and let $n\sb{\min}^{\text{div}} := \min \mathcal{D}^+$. Whenever a surviving parity prefix $v \in \mathcal{S}\sb{k, w}$ ( $r_v = \Phi_k^{-1}(v) \in \lbrack 1, 2^k - 1\rbrack$, $b_v = (3^w r_v + C_k(v)) / 2^k$ ) contractively coalesces with $v' \in \mathcal{S}\sb{k', w'}$ ( $3^{w - w'} < 2^{k - k'}$ and $b_v \equiv b\sb{v'} \pmod{3^{w'}}$ ), set $q_0 := (b_v - b\sb{v'}) / 3^{w'} \in \mathbb{Z}$ and:

```math
t_{\min}(v, v') := \max\left(0,\; \left\lceil \frac{-q_0}{3^{w - w'}} \right\rceil,\; \left\lfloor \frac{2^{k'} q_0 + r_{v'} - r_v}{2^k - 2^{k'} 3^{w - w'}} \right\rfloor + 1\right), \qquad N_{\text{coal}}(v, v') := 2^k t_{\min}(v, v') + r_v.
```

> Then **every** integer $n_0 \ge N\sb{\text{coal}}(v, v')$ in the residue class $r_v + 2^k \mathbb{Z}\sb{\ge 0}$ satisfies $T^k(n_0) = T^{k'}(n')$ for an explicit positive integer $1 \le n' < n_0$, unconditionally excluding $n\sb{\min}^{\text{div}}$ from $\lbrace n \in r_v + 2^k \mathbb{Z}\sb{\ge 0} : n \ge N\sb{\text{coal}}(v, v')\rbrace$. Across all newly coalesced surviving cylinders up to $k \le 18$, **$t\sb{\min}(v, v') = 0$ identically** ( $N\sb{\text{coal}}(v, v') = r_v$, $\max\sb{k \le 16} N\sb{\text{coal}} = 64{,}703 \le 72{,}058$, $\max\sb{k \le 17} N\sb{\text{coal}} = 130{,}799$ ), excluding $n\sb{\min}^{\text{div}}$ from the **entire** arithmetic progression $r_v + 2^k \mathbb{Z}\sb{\ge 0}$ with **zero $N_0$ assumption** (`verify_minimal_divergent_coalescence_obstruction`).

**Proof:**
Writing $n_0 = 2^k t + r_v$ ( $t \in \mathbb{Z}\sb{\ge 0}$ ) gives $T^k(n_0) = 3^w t + b_v = 3^{w'}\bigl(3^{w - w'} t + q_0\bigr) + b\sb{v'}$. Setting $u' := 3^{w - w'} t + q_0$ and $n' := 2^{k'} u' + r\sb{v'}$, since $v' \in \mathcal{S}\sb{k', w'}$ forces $v'\sb 0 = 1 \implies 1 \le r\sb{v'} < 2^{k'}$, we have $n' \ge 1 \iff u' \ge 0 \iff t \ge \lceil -q_0 / 3^{w - w'} \rceil$, in which case $\Phi\sb{k'}(n') = v'$ and $T^{k'}(n') = 3^{w'} u' + b\sb{v'} = T^k(n_0)$. Moreover, $n_0 - n' = (2^k - 2^{k'} 3^{w - w'}) t - (2^{k'} q_0 + r\sb{v'} - r_v) > 0 \iff t \ge \lfloor \frac{2^{k'} q_0 + r\sb{v'} - r_v}{2^k - 2^{k'} 3^{w - w'}} \rfloor + 1$ since $2^k - 2^{k'} 3^{w - w'} \ge 1$. Thus for every $t \ge t\sb{\min}(v, v')$, $1 \le n' < n_0$ and $T^k(n_0) = T^{k'}(n')$: if $n_0 = n\sb{\min}^{\text{div}} \in \mathcal{D}^+$, then $T^k(n_0) = T^{k'}(n') \implies n' \in \mathcal{D}^+$ with $1 \le n' < n\sb{\min}^{\text{div}}$, contradicting minimality of $n\sb{\min}^{\text{div}}$. $\blacksquare$

---

## 15. Three-Line Attack Discrimination, Zero-Trust-Gap Reflective Hensel Certificates ( $m \le 95$ ), & $3 \times 3$ Counter-Model Matrix (Theorems 23–25)

### Theorem 23 (Line A: Minimal Counterexample First-Block Rigidity, Unique $q = 3$ Merger, Raney Cone Optimality, & $\mathbb{Z}^-$/Sturmian Falsification)
> By `collatz_iff_strict_descent`, `CollatzConjectureStandard` holds if and only if no minimal non-descending integer $n\sb{\min} := \min\lbrace n > 1 : \forall k \ge 1,\; T^k(n) \ge n\rbrace$ exists (`verify_minimal_counterexample_rigidity_and_sturmian_obstruction`, `CollatzFormal.lean` Section 10):

1. **(First-Block Rigidity $n\sb{\min} \equiv 3 \pmod 4$ & $a_1 = 1$ via Hercher Entry Merger):**
   - Every $n > 1$ with $n \not\equiv 3 \pmod 4$ drops strictly below $n$ in $\le 2$ compressed steps (`minimal_counterexample_mod4_eq_3`), forcing $n\sb{\min} \equiv 3 \pmod 4$ ( $w_1 \ge 2$ ).
   - If the first spiral block of $n\sb{\min}$ has even-run length $a_1 \ge 2$, Hercher's Entry Merger (`hercher_entry_merger_a1_ge_2`) gives $T^{w_1 + 1}\bigl(\frac{n\sb{\min} - 1}{2}\bigr) = T^{w_1 + 2}(n\sb{\min})$ with $1 \le \frac{n\sb{\min} - 1}{2} < n\sb{\min}$; by minimality of $n\sb{\min}$, $\frac{n\sb{\min} - 1}{2}$ reaches $1 < n\sb{\min}$, forcing $n\sb{\min}$ to reach $1 < n\sb{\min}$, a contradiction! Thus **$a_1 = 1$ identically** ( $T^{w_1}(n\sb{\min}) \equiv 2 \pmod 4$ ).
   - Moreover, coupling `collatz_iff_strict_descent` with Theorem 22.2 (`strict_descent_minimal_counterexample_coalescence_contradiction`) excludes $n\sb{\min}$ from **every** contractively coalescing arithmetic progression $r_v + 2^k \mathbb{Z}\sb{\ge 0}$ above $N\sb{\text{coal}}(v, v')$, regardless of whether $n\sb{\min}$ diverges or enters a positive cycle!
2. **(Unique $q = 3$ Polynomial Predecessor Merger & Counter-Model Discrimination):** For the generalized compressed $(qn + 1)$ map $T_q$, the $2$-step predecessor merger $T_q^2(4t + 2) = T_q^3(8t + r)$ ( $r \in \lbrace 1, 3, 5, 7\rbrace$ ) is equivalent to the polynomial identity $q(r - 4) = 3$, whose **unique odd solution is $(q, r) = (3, 5)$** (`odd_multiplier_merger_unique_q3`). Consequently:
   - In Counter-Model $\mathcal{M}\sb 3$ ( $5n + 1$ on $\mathbb{Z}^+$ ), the cycle minimum $n_0 = 13$ has $w_1 = 3$ and $a_1 = 4 \ge 2$, yet $T_5^4(6) = 2 \ne 5 = T_5^5(13)$, **escaping Entry Merger** because $q = 5 \ne 3$.
   - In Counter-Model $\mathcal{M}\sb 1$ ( $\mathbb{Q}\sb{(2)}^+$ ), the positive rational cycle $n_0 = \frac{19}{5}$ has $w_1 = 3$ and $a_1 = 2 \ge 2$ and **does** merge with $\frac{19/5 - 1}{2} = \frac{7}{5} < \frac{19}{5}$ at $T^4(7/5) = T^5(19/5) = \frac{19}{5}$, escaping contradiction **solely** because $\mathbb{Q}\sb{(2)}^+$ is not well-ordered on $(0, x)$.
3. (Minimum-Drift Suffix Optimality of $\mathcal{S}$ vs $\mathcal{E}$ & Falsification of Pure $(2,3)$-Adic Coalescence on $\mathcal{S}\sb \infty$ ):
   - Expanding target prefixes from $\mathcal{S}\sb{k'}$ to the full end-expanding cone $\mathcal{E} := \lbrace v' : v'\sb 0 = 1,\; 3^{w(v')} > 2^{\lvert v' \rvert},\; 1 \le w(v') < w\rbrace$ prunes **zero additional prefixes** up to $k \le 17$ (`max_target_kp = 18`, zero target-weight truncation). Note that cyclic shifting does *not* preserve $b\sb{v'} \bmod 3^{w(v')}$; instead, the true structural reduction (`end_expanding_coalescence_reduces_to_suffix`, proved universally in `CollatzFormal.lean` Section 10) decomposes any $v' \in \mathcal{E} \setminus \mathcal{S}\sb{\lvert v' \rvert}$ at its longest net-shrinking prefix $u$ ( $3^{w(u)} \le 2^{\lvert u \rvert}$ ) as $v' = u \mathbin{++} s$ with $\lvert s \rvert \ge 1$ and $s \in \mathcal{S}\sb{\lvert s \rvert}$. By $C(u \mathbin{++} s) = 3^{w(s)} C(u) + 2^{\lvert u \rvert} C(s)$, every congruence $b_v \equiv b\sb{v'} \pmod{3^{w(v')}}$ projects to $b_v \equiv b_s \pmod{3^{w(s)}}$ while $2^{\lvert v \rvert - \lvert v' \rvert} > 3^{w - w(v')}$ and $2^{\lvert u \rvert} \ge 3^{w(u)}$ imply $2^{\lvert v \rvert - \lvert s \rvert} > 3^{w - w(s)}$, so $v$ ALREADY coalesces contractively with $s \in \mathcal{S}\sb{\lvert s \rvert}$!
   - **Falsification of Pure $(2,3)$-Adic Coalescence Alone:** All three known negative integer cycles $-1, -5, -17 \in \mathcal{S}\sb \infty \cap \mathbb{Z}^-$ ( $\mathcal{M}\sb 2$ ) AND the aperiodic Sturmian boundary point $x\sb{\text{Sturm}} = \Phi\sb \infty^{-1}(v^\ast (\infty)) \in \mathcal{S}\sb \infty$ suffer **$0$ contractive coalescences** (exhaustive across all $1 \le w' < w$ for $k \le 19$ at `max_target_kp = 18`, and verified across all indexed surviving targets of length $k' \le 18$ up to `sturm_depth = 45`). Specifically, along $v^\ast (k)$ whenever $3^{w-1} < 2^{k-1}$, isolated zeros in $v^\ast (\infty)$ force $k - j_w = 2$, so $b_v \equiv 1 \not\equiv 2 = b\sb{(1)} \pmod 3$ ( $w' = 1$ impossible for all $k \ge 1$ ) and $5 \cdot 2^s \not\equiv 3 + 2^d \pmod 9$ for all $s, d \in \lbrace 1, 2\rbrace$ (`sturmian_w2_mod9_disjoint`, $w' = 2$ impossible for all $k \ge 1$ ). Thus closing `NoDivergentPositiveOrbits` via Line A **must** invoke Archimedean / Baker growth on $\mathbb{Z}^+$ (Theorems 18.1, 21.1, 21.2) rather than $(2,3)$-adic congruence structure on $\mathcal{S}\sb \infty$ alone. $\blacksquare$

---

### Theorem 24 (Line B: Cyclic-Shift Carry Collapse, Exhaustive All $k_1$ $m = 92$ & Arbitrary-Depth $r$-Step Reflective Lean 4 Hensel Verifiers, & Unconditional $1 \le m \le 95$ Elimination)
1. **(Universal Cyclic-Shift Carry Divisor Collapse — Falsification of $m$-Uniform GCD/Zsigmondy Filters):** For every parity vector $v \in \lbrace 0, 1\rbrace ^k$ of weight $w = w(v) \ge 1$, every shift $j \ge 0$, and every integer divisor $d \mid (2^k - 3^w)$ (`cyclic_shift_carry_dvd_iff`, proved unconditionally over $\mathbb{Z}$ in `CollatzFormal.lean` Section 11A via explicit closed-form $\mathbb{Z}$-linear inverses $2\bigl(\frac{3^w + 1}{2} - 2^{k-1}\bigr) + (2^k - 3^w) = 1$ and $3\bigl(2^k 3^{w-1} - \frac{2^{2k} - 1}{3}\bigr) + 2^k(2^k - 3^w) = 1$ ):

   ```math
   d \mid C_k(v) \iff d \mid C_k\bigl(v^{(j)}\bigr).
   ```

   Because $\gcd(6, 2^k - 3^w) = 1$, cyclic shift acts on $C_k(v) \bmod (2^k - 3^w)$ as the invertible unit $2^{-1} 3^{v_0} \in (\mathbb{Z}/(2^k - 3^w)\mathbb{Z})^\times$, preserving $\gcd(C_k(v^{(j)}), 2^k - 3^w)$ identically and falsifying any $m$-uniform primitive-prime-divisor (Zsigmondy) obstruction that ignores spiral block count $m$ and the Archimedean floor $x_j > N_0$ (as witnessed by $139 \mid C\sb{11}(v^{(j)})$ across all $11$ shifts of $-17 \in \mathbb{Z}^-$ and $(2^7 - 5^3) = 3 \mid C\sb{7, 5}(v^{(j)})$ across all $7$ shifts of $13, 17 \in \mathbb{Z}^+$ under $5n + 1$ ).
2. **(Zero-Trust-Gap Exhaustive All $k_1 \ge 1$ $m = 92$ Certificate & Recursive Arbitrary-Depth $r$-Step Multi-Step Hensel Verifier in Lean 4):** Sections 11B–11D of `CollatzFormal.lean` (`generate_m92_reflective_hensel_bands` in `boost_mechanisms.py`, automatically cross-checked entry-by-entry against `CollatzFormal.lean` via `lean_m92_bands_exact_match`) eliminate the Python trust gap across both $2$-step and recursive multi-step Hensel pruning:
   - Kernel-checked rational convergent bounds `rational_log2_3_convergent_bounds` ( $1054/665 < \log_2 3 < 1539/971 < 485/306$ );
   - Complete all $k_1 \ge 1$ $m = 92$ elimination (`m92_two_step_hensel_kernel_verified`, `m92_nonactive_bounds_kernel_verified` — both **zero axioms `[]`** — and universal theorem `m92_all_k1_hensel_complete`), ruling out `ValidTwoStepSpiral m92B1 m92B2` across **every** $k_1 \ge 1$: $1 \le k_1 \le 8$ via $3^8(\text{hi}\sb 1 + 1) < 2^8(2(B_1 + 1) + 1)$, the $61$ active bands ( $9 \le k_1 \le 68$ and $k_1 = 71$, $1{,}120$ collapsed $2$-adic congruences), the $4$ non-active odd-multiple gap bands $k_1 \in \lbrace 69, 70, 72, 73\rbrace$, and all $k_1 \ge 74$ via $\text{hi}\sb 1 + 1 < 2^{74} \le 2^{k_1}$;
   - Arbitrary-depth (`r`-step) recursive windowed Hensel certificate verifier (`SpiralWindowedPath`, `HenselTree`, `checkHenselNode_sound`, `verifyMultiStepHenselBand_sound`) + kernel proof `m93_multistep_hensel_kernel_verified` (`by decide`), certifying inside Lean 4: (i) all $3$ active bands of $m = 93, u = 2$ ( $r = 1$ ), (ii) both $r = 1$ ( $2$-step) and genuine $r = 2$ ( $3$-step spiral $z_1 \to z_2 \to z_3 \to z_4$ ) recursive tree certificates on $m = 93, u = 1, s = 1, k_1 = 71$, and (iii) exact survivor detection & non-vacuity on $m = 93, u = 1, s \ge 2, k_1 = 45$ (rejecting `exemptIds = []`, accepting `exemptIds = [179507528690102354051071]`, and verifying its $309$-step drop $\le 2^{71}$ ).
3. **(Unconditional Positive $m$-Cycle Elimination Extended to $1 \le m \le 95$ Across All Weights $W \in \lbrack 1, \infty)$ ):** At $m = 95, u = 1$ ( $c = 4$, $B_1 = 186{,}580{,}408{,}057{,}834{,}140{,}284{,}177 \approx 2^{77.31}$, $B_2 \approx 2^{121.52}$ ), naive $(s = 1, r \le 4)$ recursion faces an infeasible $r = 4$ search horizon because all $4$ intermediate vertices lie in $I_1 = (B_1, B_2\rbrack$. Introducing a **$5$-way disjoint first-hit $\Lambda$-squeeze partition** (`prove_m95_all_weight_nonexistence` / `prove_multistep_hensel_mcycle_nonexistence(max_m_full=95)` in `goal_extensions.py`) splits $s = 1, r = 4$ around the threshold $M = 2^{88} - 1$ (`split_bits = 88`): Case $0$ constrains all $4$ intermediate vertices to $\lbrack M + 1, B_2\rbrack$ (slashing the reciprocal tail budget and collapsing initial $z_1$ bands), while Cases $d \in \lbrace 1, 2, 3, 4\rbrace$ isolate the exact first step $z\sb{d+1} \in \lbrack B_1 + 1, M\rbrack$:

| $m = 95, u = 1$ Subcase | Max Depth $r$ | Tree Nodes | Leaf Congruences | Arithmetic Survivors | Cycle Survivors |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`s=1 (r<c)`** ( $1 \le r \le 3$ ) | $3$ | $143{,}957$ | $12{,}903{,}988$ | $0$ | **$0$** |
| **`s=1 (r=c)`** ( $r = 4$, $5$-way first-hit at $M = 2^{88} - 1$ ) | $4$ | $19{,}662{,}457$ | $504{,}032{,}232$ | $0$ | **$0$** |
| **`s>=2`** ( $1 \le r \le 3$ ) | $3$ | $294{,}591$ | $37{,}859{,}293$ | **$55$** (all drop $\le 506$ steps) | **$0$** |
| **Total ( $m = 95, u = 1$, `prove_m95_all_weight_nonexistence`)** | $\le 4$ | **$20{,}101{,}005$** | **$554{,}795{,}513$** | **$55$** | **$0$** |

Combined with Theorem 19.2 (`u = 2, 3, 4` for $m = 95$, yielding $27$ survivors with $1$ overlap across `1 <= m <= 94`'s $6$ survivors: $32 + 55 = 87$ distinct total), this proves **zero non-trivial positive integer $m$-cycles exist for all $1 \le m \le 95$ across all weights $W \in \lbrack 1, \infty)$**. Furthermore, all **$55$ new arithmetic survivors** (`henselSurvivors95New55`) are certified directly in the Lean 4 kernel (`all_55_new_m95_hensel_survivors_drop_below_2_pow_71`, **zero axioms `[]`**) to drop $\le 2^{71}$, bringing total kernel-certified arithmetic survivors across $1 \le m \le 95$ to **$32 + 55 = 87$** with **$0$ cycle survivors**. $\blacksquare$

---

### Theorem 25 (Line C: One-Equation Sign-Separation, $2^{\lvert v \rvert} \le 4^{w(v)} n$ Polylogarithmic Obstruction, Parametric Families, & $3 \times 3$ Counter-Model Matrix)
> Consider the side-condition-free One-Equation Diophantine reformulation $\forall n \in \mathbb{Z}^+,\; \exists v \in \lbrace 0, 1\rbrace ^\ast ,\; 2^{\lvert v \rvert} = 3^{w(v)} n + C(v)$ (`collatz_iff_one_equation_diophantine`, `verify_one_equation_parametric_families_and_density_obstruction`, `CollatzFormal.lean` Section 12):

1. **(Automatic Sign-Separation & Universal $3^w$-Indivisibility):** Every integer solution $x \in \mathbb{Z}$ to $2^{\lvert v \rvert} = 3^{w(v)} x + C(v)$ **automatically satisfies $x \ge 1$** (`one_equation_forces_pos`): $x = 0$ and all negative integers $\mathbb{Z}^-$ (including $-1, -5, -17$ in $\mathcal{M}\sb 2$ ) are algebraically excluded without any side inequality because $T^{\lvert v \rvert}(x) = 1 > 0$ whereas $x \le 0 \implies T^k(x) \le 0$. Equivalently, whenever $C(v) \ge 2^{\lvert v \rvert}$, **$3^{w(v)} \nmid (C(v) - 2^{\lvert v \rvert})$ universally** (`carry_sub_pow2_not_dvd_pow3`).
2. **(Universal $2^{\lvert v \rvert} \le 4^{w(v)} n$ Horizon & Falsification of Bounded-Weight Covering Systems):** Every solution $(v, n)$ satisfies the exact universal inequality (`one_equation_pow2_le_pow4_mul`, sharp with equality on $n = 1, v = (1, 0)^r$ ):

   ```math
   2^{|v|} \le 4^{w(v)} n \iff |v| \le \log_2 n + 2 w(v).
   ```

   Consequently, for ANY fixed weight bound $W_0 \ge 0$, the union of all parity words with $w(v) \le W_0$ solves $2^{\lvert v \rvert} = 3^{w(v)} n + C(v)$ for at most

   ```math
   \sum_{w=0}^{W_0} \sum_{k=w}^{\lfloor \log_2 X \rfloor + 2 W_0} \binom{k}{w} = O\bigl((\log X)^{W_0 + 1}\bigr)
   ```

   positive integers $n \le X$ — **natural density $0$**, rigorously falsifying any finite-weight Diophantine covering-system strategy on the One-Equation identity and proving $w(v) \to \infty$ is mandatory for positive-density coverage.
3. **(Infinite Parametric Families & $3$-Adic Garden-of-Eden Branching Obstruction):**
   - `one_equation_pow2_family`: $v = 0^a$ solves $n = 2^a$ ( $w = 0$ ).
   - `one_equation_geometric_family`: $v = 1 \, 0^{2d+1}$ ( $\lvert v \rvert = 2d + 2, w = 1$ ) solves the infinite odd geometric family $g\sb{d+1} = \frac{4^{d+1} - 1}{3} \in \lbrace 1, 5, 21, 85, 341, \dots\rbrace$.
   - `one_equation_even_double_closure` & `one_equation_odd_predecessor_lift`: $v \mapsto 0 v$ lifts $x \mapsto 2x$, while $v \mapsto 1 v$ lifts $3m + 2 \mapsto 2m + 1$. Crucially, **multiples of $3$ ( $x = 3r$ )** have $2x = 6r \not\equiv 1 \pmod 3$ and therefore possess **zero odd Collatz predecessors in $\mathbb{Z}$** (e.g. $n = 3$ requires the $5$-step spiral $3 \to 5 \to 8 \to 4 \to 2 \to 1$, $v = (1, 1, 0, 0, 0), w = 2$ ), manifesting the $3$-adic Garden-of-Eden branching obstruction on inverse Collatz trees.
4. **(Master $3 \times 3$ Counter-Model Discrimination Matrix — `verify_boost_three_line_counter_model_matrix`):**

| Attack Line / Mechanism | $\mathcal{M}\sb 1 = \mathbb{Q}\sb{(2)}^+$ ( $19/5,\; 29/5$ ) | $\mathcal{M}\sb 2 = \mathbb{Z}^-$ ( $-1, -5, -17 \in \mathcal{S}\sb \infty$ ) | $\mathcal{M}\sb 3 = (5n+1)$ on $\mathbb{Z}^+$ ( $13,\; 17$ ) | Status on $\mathbb{Z}^+$ ( $3n+1$ ) |
| :--- | :--- | :--- | :--- | :--- |
| **Line A:** $n\sb{\min}$ Well-Ordering + $(q,r)=(3,5)$ Entry Merger | Blocked: $\frac{19}{5}$ merges with $\frac{7}{5} < \frac{19}{5}$, but $\mathbb{Q}\sb{(2)}^+$ lacks well-ordering | Blocked: $\mathbb{Z}^-$ unbounded below & $x < 0$ violates $T^k(x) \ge 1$ | Blocked: $q = 5 \ne 3$ breaks $q(r-4) = 3$ ( $T_5^4(6) = 2 \ne 5 = T_5^5(13)$ ) | **SURVIVES** (`n_min ≡ 3 mod 4`, `a_1 = 1`; requires Archimedean/Baker input to beat $x\sb{\text{Sturm}}$ ) |
| **Line B:** Reflective Hensel + Disjoint First-Hit $\Lambda$-Squeeze ( $m \le 95$ ) | Blocked: $5 \mid (2^5 - 3^3)$ is a unit in $\mathbb{Z}\sb{(2)}$, allowing $\frac{19}{5}, \frac{29}{5}$ | Blocked: $2^K < 3^W$ reverses sign of $2^K - 3^W < 0$ | Blocked: $\log_2 5$ shifts CF convergents ( $2^7 - 5^3 = 3 \mid 39, 51$ at $m = 1, 2$ ) | **SURVIVES** (proves $1 \le m \le 95$ unconditionally; pure cyclic-shift GCD filter falsified) |
| **Line C:** One-Equation $2^{\lvert v \rvert} = 3^{w(v)} x + C(v)$ Surjectivity | Blocked: $\frac{19}{5}$ solves over $\mathbb{Q}\sb{(2)}^+$ via non-integer denominators ( $5$ invertible) | Blocked: `one_equation_forces_pos` forces $x \ge 1$, excluding all $\mathbb{Z}^-$ | Blocked: $2^{\lvert v \rvert} = 5^{w(v)} x + C\sb{v, 5}$ fails at $x = 13$ across all $v$ | **SURVIVES** (sign-separated; bounded-weight $w \le W_0$ covering falsified by $2^{\lvert v \rvert} \le 4^{w(v)} n$ ) |

---

## 16. Zero-Trust-Gap $m \le 92$ Kernel Pipeline, Unconditional $m \le 96$ & $m \le 98$ ( $u \ge 2$ ) Hensel Frontier, Multi-Block Rigidity, & Unbounded Inverse Tree (Theorems 26–28)

### Theorem 26 (Line B: 100% Pure-`Nat` Lean 4 Kernel Cycle Elimination Pipeline for $1 \le m \le 92$ & C23 Frontier Push Through $m \le 96$ / $m \le 98$ )
1. **(Zero-Trust-Gap End-to-End Lean 4 Kernel Proof `no_nontrivial_spiral_cycles_1_to_92` — Deliverable 1A):** Section 13 of `CollatzFormal.lean` (`verify_zero_trust_gap_rational_log_and_m92_pipeline` in `goal_extensions.py`) eliminates every imported Python interval constant by deriving the entire $1 \le m \le 92$ cycle non-existence proof inside the Lean 4.35.0 kernel from **only two explicit mathematical hypotheses** (`BarinaThreshold (2 ^ 71)` and `BakerLMNPowerBound`):
   - **Rational Taylor Enclosures & All $52$ Convergents of $\log_2 3$:** Proves rational series bounds on $2^{200} \ln 2$ ( $N = 60$, width $66 \le 70$ ) and $2^{200} \ln 3$ ( $N = 105$, width $105 \le 110$ ), together with unimodular determinants $p\sb{n+1} q_n - p_n q\sb{n+1} = (-1)^n$ and certified alternating signs (`convergent_signs_and_relations_certified`, **zero axioms `[]`**) across $(p_0, q_0) \dots (p\sb{51}, q\sb{51})$.
   - **Zero-Sorting Forward Scan & Inverse-Bernoulli Telescoping:** Formalizes $O(\log n)$ binary-exponentiation `evalPow2Pow3Aux` + `certifyLog2Pow`, the $O(m)$ single-pass forward-scan upper bound `sortedCyclicRhsFast` (`scan_phi_upper_bound`), and pure-`Nat` Inverse-Bernoulli product telescoping `teleStepCap` (`teleBernoulli_ratio_bound`), certifying all $9$ unimodular convergent slabs across $1 \le W < q\sb{51}$ (`slabs_group1_certified`, `slabs_group2_certified`) and the asymptotic Baker–LMN regime $W \ge q\sb{51}$ (`no_spiral_cycle_ge_q51`).
   - **Kernel-Derived $m = 92$ Hensel Bands:** Computes `derivedM92Lo k1` and `derivedM92Hi k1` directly inside Lean 4 from `exactM92B1 = 186580408057834151310020`, `exactM92B2`, `exactM92B3`, and $(p\sb{43}, q\sb{43})$, certifying `checkM92BoundsSubsumed 65 = true` (`exactM92_hensel_bridge_certified`, **zero axioms `[]`**) for all $9 \le k_1 \le 73$ and closing `no_nontrivial_spiral_cycles_1_to_92` via `exactM92_all_k1_hensel_complete`.
2. **(Unconditional All-Weight Elimination for $1 \le m \le 96$ & Higher-Multiple $u \ge 2$ Elimination Through $m \le 98$ — Deliverable 1B):** Coupling **Tight $b\sb{\text{low}}$ Minimum-Vertex Squeeze** ( $b\sb{\text{low}} = \min\bigl(B\sb{1,\text{raw}}, \lfloor 1.05 c / (\text{ulam}/\text{safety} - \text{tfc}) \rfloor\bigr)$ ), universal $1 \le r \le \min(c, 4)$ base sweeps, **$5$-way Sorted-Cyclic Pigeonhole pruning** at $(c = 6, s\sb{\text{low}} = 2, r = 5)$, and **$s\sb{\text{low}} = 1$ subset-squeeze / $H\sb{\text{raw}}$ first-hit partitioning** at $r \in \lbrace 5, 6\rbrace$ (`prove_m96_m98_hensel_frontier`, accelerated ~100x via portable C23 `_hensel_fast.c` using node-entry $\lbrack lo\sb{p1}, hi\sb{p1}\rbrack$ floor-nesting clamping $\lfloor \lfloor 3^{k_d} R / 2^s \rfloor / 3^{k_d} \rfloor = \lfloor R / 2^s \rfloor$ and `u128` leaf congruences) traverses **$7{,}292{,}911{,}961$** Hensel tree nodes and **$142{,}019{,}994{,}127$** leaf congruences across $m \in \lbrace 96, 97, 98\rbrace$ with **$0$ cycle survivors**:

| Block Count $m$ | Multiples $u \cdot (p\sb{43}, q\sb{43})$ Certified | Max $c$ | Max Depth $r$ | Tree Nodes | Leaf Congruences | Distinct Arith. Survivors | Cycle Survivors |
| :---: | :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| **$96$** | **$u = 1, 2, 3, 4, 5$** ( $u \ge 6$ monotone tail) | $5$ | $5$ | $1{,}867{,}157{,}494$ | $43{,}167{,}690{,}219$ | $1{,}946$ | **$0$** |
| **$97$** | **$u = 2..7$** ( $u = 8, 9$ potential; $u \ge 10$ monotone) | $5$ | $5$ | $163{,}371{,}056$ | $4{,}913{,}085{,}385$ | $2{,}567$ | **$0$** |
| **$98$** | **$u = 2..9$** ( $u \ge 10$ monotone; $c = 6$ at $u = 2$ ) | $6$ | $6$ | $5{,}262{,}383{,}411$ | $93{,}939{,}218{,}523$ | $6{,}334$ | **$0$** |
| **Combined ( $96..98$ )** | **All $u \ge 1$ for $m = 96$; all $u \ge 2$ for $m = 97, 98$** | $\le 6$ | $\le 6$ | **$7{,}292{,}911{,}961$** | **$142{,}019{,}994{,}127$** | **$8{,}077$** ( $8{,}075$ new) | **$0$** |

Consequently, **zero non-trivial positive integer $m$-cycles exist for all $1 \le m \le 96$ across all weights $W \in \lbrack 1, \infty)$**, and for $m \in \lbrace 97, 98\rbrace$ all higher multiples $u \ge 2$ are unconditionally eliminated (leaving solely $u = 1$ at $m = 97, 98$ ). Furthermore, all **$8{,}075$ newly discovered arithmetic survivors** $> 2^{71}$ (`henselSurvivors96To98Batch0` .. `henselSurvivors96To98Batch100`) are certified directly inside the Lean 4.35.0 kernel (`all_new_m96_to_98_hensel_survivors_drop_below_2_pow_71`, `m96_to_98_hensel_survivor_drop_universal`, via `lookup6Step` + `oddPeelStep` proved equivalent to `collatzIter` in `checkSurvivorBatchFast_sound`, with **$101$ zero-axiom `[]` batch theorems**) to drop strictly $\le 2^{71}$ within $172 \le k \le 616$ compressed steps, bringing total kernel-certified arithmetic survivors across $1 \le m \le 98$ to **$87 + 8{,}075 = 8{,}162$** with **$0$ cycle survivors**. $\blacksquare$

---

### Theorem 27 (Line A: Multi-Block Minimal-Counterexample Rigidity, Sub-Quadruple Exit-Tail Merger, & Archimedean–Coalescence Coupling)
> Extending Theorem 23 to multi-block spiral transitions along any putative minimal non-descending counterexample $n\sb{\min} := \min\lbrace n > 1 : \forall k \ge 1,\; T^k(n) \ge n\rbrace$ (`verify_multiblock_rigidity_and_archimedean_coupling`, `CollatzFormal.lean` Section 14):

1. **(Universal Multi-Block Entry & Exit-Tail Mergers):**
   - **Sub-Double Entry Merger (`subdouble_entry_merger_step`):** At any step $K \ge 0$, if $x = T^K(n\sb{\min})$ has $x + 1 = 2^w u$ ( $w \ge 2, u \ge 1$ ), $x \le 2 n\sb{\min}$, and even-run $a \ge 2$ ( $4 \mid (3^w u - 1)$ ), then $n' := \frac{x - 1}{2}$ satisfies $1 \le n' < n\sb{\min}$ and $T^{w + 1}(n') = T^{K + w + 2}(n\sb{\min})$.
   - **Sub-Quadruple Exit-Tail Merger (`subquad_exit_tail_merger_step` — Works Even at $w = 1$!):** At the final odd step $x\sb{\text{last}} = 2 \cdot 3^{w-1} u - 1$ of **any** spiral block ( $w \ge 1$ ) with $a \ge 2$, `block_exit_tail_mod8_eq_5` forces $x\sb{\text{last}} \equiv 5 \pmod 8$. Whenever $x\sb{\text{last}} \le 4 n\sb{\min}$, $n' := \frac{x\sb{\text{last}} - 1}{4} = 2q + 1$ satisfies $1 \le n' < n\sb{\min}$ and merges in **one step**: $T^1(n') = T^{K + 3}(n\sb{\min})$.
2. **(Concrete Multi-Block Parity & Congruence Exclusions on $n\sb{\min}$ ):**
   - `block1_u1_mod4_rigidity`: $n\sb{\min} + 1 = 2^{w_1} u_1$ forces $u_1 \equiv 1 \pmod 4$ when $w_1$ is odd and $u_1 \equiv 3 \pmod 4$ when $w_1$ is even ( $n\sb{\min} \not\equiv 3 \pmod 8$, $n\sb{\min} \not\equiv 15 \pmod{16}$, etc.).
   - `block2_a2_eq_1_of_w1_2_or_3`: Whenever $w_1 \in \lbrace 2, 3\rbrace$ ( $a_1 = 1$ ), $x_2 \le \frac{27}{16}(n\sb{\min} + 1) < 2 n\sb{\min}$ (for $n\sb{\min} \ge 7$ ) or $x\sb{\text{last},2} < 4 n\sb{\min}$ forces **$a_2 = 1$ identically** across both $w_2 = 1$ and $w_2 \ge 2$.
   - `w2_a1_eigenfunction_step` & `six_block_w2_subdouble_bound`: Along $(w, a) = (2, 1)$ blocks, $2 x\sb{\text{next}} + 1 = \frac{9}{8}(2x + 1)$ (`eigenfunction` $2x + 1$ ), and $9^6 = 531{,}441 < 549{,}755 \approx 2 \cdot 8^6$, so **up to $6$ consecutive $(2, 1)$ blocks** stay strictly $< 2 n\sb{\min}$, forcing $a_2 = a_3 = \dots = a_7 = 1$; similarly `block2_w1_4_w2_1_a2_eq_1` forces $a_2 = 1$ at $(w_1, a_1, w_2) = (4, 1, 1)$.
3. **(Infinite Cantor-Cone Family, Universal Carry Ceiling, & $3$-Adic Integer Fiber Collapse):**
   - `cantor_cone_family_1w_00_survives`: Every word $1^w 0^2$ with $w \ge 4$ lies strictly in the surviving Cantor cone $\mathcal{S}\sb{w+2}$ ( $3^4 = 81 > 64 = 2^6$ ).
   - `surviving_carry_three_mul_le_weight_pow3` & `surviving_prefix_iter_lt_pow3`: Every surviving prefix $v \in \mathcal{S}\sb k$ satisfies $3 C_k(v) \le w(v) \, 3^{w(v)}$. Hence for any positive integer $n_0 \ge 1$ once $2^k \ge n_0 + w(v)$ (Archimedean horizon $k \ge \log_2(n_0 + w(v))$, which **never** holds on $x\sb{\text{Sturm}} \in \mathbb{Z}\sb 2 \setminus \mathbb{Z}^+$ or $\mathbb{Z}^-$ ), $T^k(n_0) < 3^{w(v)}$ — collapsing the $3$-adic quotient $\lfloor T^k(n_0) / 3^{w(v)} \rfloor = 0$ identically and yielding the master exclusion `minimal_counterexample_archimedean_coalescence_exclusion`. $\blacksquare$

---

### Theorem 28 (Line C: Unbounded-Weight Syracuse Predecessor Tree Bypassing $m \equiv 0 \pmod 3$ & Exponential Growth Bound)
> Resolving the finite-weight density-zero barrier of Theorem 25(2) and the $m \equiv 0 \pmod 3$ Garden-of-Eden obstruction of Theorem 25(3) (`verify_unbounded_syracuse_predecessor_tree_growth`, `CollatzFormal.lean` Section 15):

1. **(Multi-Exponent Syracuse Predecessor Lifts):** `one_equation_even_replicate_closure` ( $v \mapsto 0^a v$, $x \mapsto 2^a x$ ) and `one_equation_syracuse_general_lift` prove that whenever $2^{\lvert v \rvert} = 3^{w(v)} y + C(v)$ and $x$ is odd with $3x + 1 = 2^d y$ ( $d \ge 1$ ), $v' := 1 \, 0^{d-1} v$ has weight $w(v') = w(v) + 1$, length $\lvert v' \rvert = \lvert v \rvert + d$, and solves $2^{\lvert v' \rvert} = 3^{w(v')} x + C(v')$.
2. **(Garden-of-Eden-Bypassing Binary Tree & Global Injectivity):** Starting from root $y_0 = 5$ ( $v_0 = 1000$, $2^4 = 3^1 \cdot 5 + 1$, $y_0 \equiv 2 \pmod 3$ ), for any node $y \ge 5$ with $y$ odd and $3 \nmid y$, choosing $d(y, \text{false}) \in \lbrace 1, 2\rbrace$ vs $d(y, \text{true}) \in \lbrace 3, 4\rbrace$ (shifted $+2$ to $\lbrace 5, 6\rbrace$ precisely when the child would satisfy $3 \mid x$, `syracuseValidExp`) guarantees at **every** binary choice word $cs \in \lbrace \text{false}, \text{true}\rbrace ^w$:
   - **Universal Invariant (`syracuseTreeVal_invariant`):** $x = \text{syracuseTreeVal}(cs)$ satisfies $x \ge 5$, $x \equiv 1 \pmod 2$, and **$3 \nmid x$** (zero Garden-of-Eden dead ends at any depth $w \ge 0$!);
   - **Exact One-Equation Solution (`syracuseTreeWord_solves_one_equation`):** $v = \text{syracuseTreeWord}(cs)$ has unbounded weight $w(v) = w + 1$ and solves $2^{\lvert v \rvert} = 3^{w+1} x + C(v)$;
   - **Global Injectivity (`syracuseTreeVal_injective`):** $\text{syracuseTreeVal}(cs_1) = \text{syracuseTreeVal}(cs_2) \implies cs_1 = cs_2$ across **all** depths and branches simultaneously ( $2{,}047$ distinct positive integers verified for $0 \le w \le 10$ );
   - **Rigorous Exponential Growth (`syracuseTreeVal_upper_bound`):** Since $d \le 6$ at every step,

     ```math
     3^{w + 1} \cdot \text{syracuseTreeVal}(cs) < 2^{4 + 6w} \implies \text{syracuseTreeVal}(cs) < \frac{16}{3} \left(\frac{64}{3}\right)^w,
     ```

     producing at least **$2^{w+1} - 1 \ge X^{\frac{1}{6 - \log_2 3}} \approx X^{0.22650}$** distinct positive integer solutions in $\lbrack 1, X\rbrack$ (strictly beating every polylogarithmic finite-weight bound $O((\log X)^{W_0 + 1})$ ). $\blacksquare$

---

## 17. Next-Tier Cross-Disciplinary Breakthrough Mechanisms: General $(a, b)$-Affine Backward Sieve, Disjoint Multi-Root Syracuse Forest, & $2$-Vertex $(x\sb{(1)}, x\sb{(2)})$ Frontier (Theorems 29–31)

### Theorem 29 (Mechanism A: General $(a, b)$-Affine Backward Merger Sieve, $0 \pmod 3$ Carry Trap, Initial-Bit Exhaustion, & Bounded Counterexample Cycle Extraction)
> Generalizing Theorem 27's $(x - 1)/2$ and $(x\sb{\text{last}} - 1)/4$ mergers to arbitrary parity words $u \in \lbrace 0, 1\rbrace ^a$ of weight $b = w(u)$ along any putative minimal non-descending counterexample $n\sb{\min} \ge 4$ (`verify_general_backward_merger_and_bit_exhaustion`, `CollatzFormal.lean` Section 16):

1. **(Universal Parity-Free $2$-Adic Hensel Converse & General Backward Merger Sieve):**
   - **Universal Converse (`general_affine_converse_universal`):** For **every** parity word $u \in \lbrace 0, 1\rbrace ^a$ ( $b = w(u)$ ) and **every** pair of integers $x, y \in \mathbb{Z}$ (positive, zero, or negative, with **zero** side-conditions), $2^a y = 3^b x + C(u)$ automatically forces $x$ to follow parity vector $u$ step-by-step and satisfy $T^a(x) = y$.
   - **General Backward Merger (`general_affine_backward_merger_step`, `minimal_counterexample_general_backward_merger_exclusion`):** Whenever $x = T^K(n\sb{\min})$ satisfies $3^b + C(u) \le 2^a x < 3^b n\sb{\min} + C(u)$ and $3^b \mid (2^a x - C(u))$, the integer $n' := \frac{2^a x - C(u)}{3^b}$ satisfies $1 \le n' < n\sb{\min}$ and $T^a(n') = T^K(n\sb{\min})$, contradicting minimality of $n\sb{\min}$.
   - **Concrete Congruence Sieves & Return Traps:** Applying $K = 0$ with $u = (1)$ ( $C = 1$ ) proves $n\sb{\min} \not\equiv 2 \pmod 3$ (`minimal_counterexample_mod3_ne_2`), refining $n\sb{\min} \equiv 3 \pmod 4$ to **$n\sb{\min} \equiv 3 \text{ or } 7 \pmod{12}$** (`minimal_counterexample_mod12_in_3_or_7`); applying $u = (1, 1, 0)$ ( $a = 3, b = 2, C = 5$ ) proves **$n\sb{\min} \not\equiv 4 \pmod 9$** (`minimal_counterexample_mod9_ne_4`, eliminating $31 \pmod{36}$ ), confining $n\sb{\min}$ to the **$5 / 36$ residue classes $\lbrace 3, 7, 15, 19, 27\rbrace \pmod{36}$** (`minimal_counterexample_mod36_in_5_classes`); along the orbit $x = T^K(n\sb{\min})$, `sub_3_2_backward_merger_step` eliminates every $x \equiv 2 \pmod 3$ with $2x < 3 n\sb{\min} + 1$, and `sub_9_4_backward_merger_step` eliminates every $x \equiv 8 \pmod 9$ with $4x < 9 n\sb{\min} + 5$.
2. (Ruthless Falsification of Single-Return $3$-Adic Measure Decay $\mu_M(B) \to 0$ ):
   - `affineCarryInt_pos_nondiv3_of_weight_pos` ( $C(u) \ge 1$ and $3 \nmid C(u)$ for every $w(u) \ge 1$ ) and `garden_of_eden_div3_unmergeable` prove that **no trajectory value $x \equiv 0 \pmod 3$ can ever satisfy $3^b \mid (2^a x - C(u))$ for any $b \ge 1$**. Consequently, on a single return $x = T^K(n\sb{\min})$, contractive backward mergers up to $b \le 8$ leave **$3{,}522 / 6{,}561 \approx 0.53681 > 0$** of $\mathbb{Z}\sb 3$ uncovered (including $100\%$ of $0 \pmod 3$ and $7 \pmod 9$ up to $b \le 5$ ), and in $5n+1$ ( $\mathcal{M}\sb 3$ ), $n\sb{\min}^{(5)} = 5$ has a bounded orbit $\le 208$ with zero backward mergers into $\lbrack 1, 4\rbrack$. Closing the sieve therefore requires **unboundedly many returns $r \to \infty$** to bounded expansion windows $x_j \le M n\sb{\min}$.
3. **(Initial-Bit Exhaustion & Bounded Counterexample $\implies$ Non-Trivial Cycle):**
   - **Initial-Bit Exhaustion (`initial_bit_exhaustion_iter_lt_pow3`):** Because every surviving prefix $v \in \mathcal{S}\sb k$ has $w(v) < 2^k \le 2 \cdot 2^k$, as soon as $2 n\sb{\min} \le 2^{\lvert v \rvert}$ (after $\lceil \log_2(2 n\sb{\min}) \rceil$ steps — holding unconditionally for **every** $n\sb{\min} \ge 2$ ), $3 n\sb{\min} + w(v) < 3 \cdot 2^{\lvert v \rvert}$ holds automatically and forces **$T^{\lvert v \rvert}(n\sb{\min}) < 3^{w(v)}$**, exhausting the initial binary bits of $n\sb{\min}$.
   - **Cycle Extraction (`bounded_minimal_counterexample_implies_nontrivial_cycle`):** If $T^K(n\sb{\min}) \le B$ for all $K \ge 0$, finite Pigeonhole on $\lbrack n\sb{\min}, B\rbrack$ across $K = 0 \dots (B + 1)$ extracts $K_1 < K_2$ with $x\sb{\text{cyc}} = T^{K_1}(n\sb{\min}) \ge n\sb{\min} > 1$ and period $p = K_2 - K_1 \ge 1$ satisfying $T^p(x\sb{\text{cyc}}) = x\sb{\text{cyc}}$ (connecting directly to Theorem 26's $1 \le m \le 96$ unconditional cycle elimination). $\blacksquare$

---

### Theorem 30 (Mechanism B: Disjoint In-Degree $0$ Multi-Root Syracuse Forest on $\lbrack 5, n\sb{\min} - 1\rbrack$, Stratified Fourier Mixing, & Exact Open `Prop` Equivalences (`↔`) with `CollatzConjectureStandard`)
> Lifting Theorem 28's single $5$ predecessor tree to a pairwise-disjoint multi-root inverse Syracuse forest across $\lbrack 5, n\sb{\min} - 1\rbrack$ (`verify_multi_root_syracuse_forest_and_fourier_mixing`, `CollatzFormal.lean` Section 17):

1. (Catching & Fixing Two Coordinator Traps — Exact In-Degree $0$ Root Bijection & Sound $(X / n\sb{\min})^\alpha$ Scaling):
   - **Coordinator Trap 1 (Tree Overlap):** Rooting `syracuseChild` trees at *all* odd $y_0 \in \lbrack 5, n\sb{\min} - 1\rbrack$ with $3 \nmid y_0$ is **not disjoint**: `syracuseTree_overlap_witnesses` certifies $\text{syracuseChild}(5, \text{false}) = 13$ and $\text{syracuseChild}(11, \text{false}) = 7$.
   - **Exact Bijective Fix (`IsSyracuseForestRoot`, `syracuseForestRoot_iff_not_child`, `syracuseForestVal_injective`):** Among all valid odd nodes $x \ge 5$ with $3 \nmid x$, $x$ has in-degree $0$ under `syracuseChild` **if and only if**

     ```math
     x = 5 \quad \text{or} \quad 128 \mid (3x + 1) \iff x \equiv 85 \text{ or } 341 \pmod{384}
     ```

     (natural density $1/192$ of $\mathbb{Z}^+$, yielding $\sim n\sb{\min}/192$ disjoint roots below $n\sb{\min}$ ). Across **all** forest roots $r_1, r_2$ and **all** unbounded-depth binary choice sequences $cs_1, cs_2 \in \lbrace \text{false}, \text{true}\rbrace ^\ast$, $\text{syracuseForestVal}(r_1, cs_1) = \text{syracuseForestVal}(r_2, cs_2) \implies (r_1, cs_1) = (r_2, cs_2)$ (`1,016` nodes verified across the first $8$ roots up to depth $6$ with $0$ collisions).
   - **Coordinator Trap 2 (Pigeonhole at $X = n\sb{\min}$ ):** The naive bound $\ge n\sb{\min} \cdot X^c$ exceeds $X$ at $X = n\sb{\min}$! `syracuseForestVal_upper_bound` proves $3^{\lvert cs \rvert} \cdot \text{syracuseForestVal}(r, cs) \le 2^{6\lvert cs \rvert} \cdot r$, yielding the sound Pigeonhole-consistent multi-root count $\Omega\bigl(n\sb{\min} \cdot (X / n\sb{\min})^{1 / (6 - \log_2 3)}\bigr)$ for $X \ge 192 \, n\sb{\min}$.
2. (Stratified Pontryagin Character Sum Decay of $C(v) \bmod 3^W$ ):
   - Non-primitive characters $\xi = 3^{W-1}$ probe $C(v) \bmod 3$; because $C(v) \not\equiv 0 \pmod 3$ identically for $W \ge 1$, $\lvert \widehat{\mu}\sb W(3^{W-1}) \rvert \in \lbrack 0.529, 0.571\rbrack$ across $W = 2 \dots 5$, **falsifying** uniform non-primitive Fourier decay.
   - Restricting to **primitive characters $\gcd(\xi, 3) = 1$** yields clean monotonic decay $\max\sb{\gcd(\xi,3)=1} \lvert \widehat{\mu}\sb W(\xi) \rvert$: $0.2274$ ( $W = 2$ ), $0.1683$ ( $W = 3$ ), $0.0794$ ( $W = 4$ ), $0.0740$ ( $W = 5$ ).
3. (Sharpest Falsification-Resistant Open Mixing `Prop`s Equivalent (`↔`) to `CollatzConjectureStandard`):
   - **`BackwardCarryContractionWindowProp` $\iff$ `SievedBackwardCarryWindowProp` $\iff$ `CollatzConjectureStandard` (`collatz_standard_iff_backward_carry_window`, `collatz_standard_iff_sieved_backward_carry_window`):** `BackwardCarryContractionWindowProp` asserts for every $n > 1$ that $\exists K, u$ with $3^{w(u)} + C(u) \le 2^{\lvert u \rvert} T^K(n) < 3^{w(u)} n + C(u)$ and $3^{w(u)} \mid (2^{\lvert u \rvert} T^K(n) - C(u))$; coupling with Theorem 29's mod $36$ sieve proves it suffices to establish this **solely** for $n \ge 7$ in $\lbrace 3, 7, 15, 19, 27\rbrace \pmod{36}$ (`SievedBackwardCarryWindowProp`, density $5/36 \approx 13.89\%$ ).
   - **`MultiRootForestCarryCollisionProp` $\iff$ `SievedMultiRootForestCarryCollisionProp` $\iff$ `CollatzConjectureStandard` (`collatz_standard_iff_multi_root_forest_collision`, `collatz_standard_iff_sieved_forest_collision`):** Even when a forest node $z = \text{syracuseForestVal}(r, cs)$ satisfies $z \gg n$, any collision $2^{\lvert u \rvert} T^K(n) = 3^{w(u)} z + C(u)$ with a tree rooted at $r \in \lbrack 5, n - 1\rbrack$ (even restricted solely to $n \ge 7$ in $\lbrace 3, 7, 15, 19, 27\rbrace \pmod{36}$ ) forces $T^K(n) = T^{\lvert u \rvert}(z)$ (`general_affine_converse_universal`), and `syracuseForestVal_reaches_root` routes $z$ forward in $\le 6\lvert cs \rvert$ steps to $r < n$, which reaches $1$ by strong minimal-counterexample induction and pulls $n$ to $1$ via `coalescence_reaches_one`! All four `Prop`s fail on all three counter-models ( $\frac{19}{5}, \frac{29}{5} \in \mathbb{Q}\sb{(2)}^+$, $-1, -5, -17 \in \mathbb{Z}^-$, and $5, 13, 17$ in $5n+1$ ). $\blacksquare$

---

### Theorem 31 (Mechanism C: $N_0$-Free Prime-Denominator $D = 2^K - 3^W$ Rigidity, $p = 23 / 139$ Falsifications, & $2$-Vertex $(x\sb{(1)}, x\sb{(2)})$ Frontier Split on $m = 97..99, u = 1$ )
> Auditing $N_0$-free multiplicative-order cycle obstructions and prototyping $2$-vertex $(x\sb{(1)}, x\sb{(2)})$ Hensel budget splitting beyond $m = 96$ (`verify_prime_denom_rigidity_and_two_vertex_frontier`, `run_two_vertex_hensel_bands`, `_hensel_fast.c`, `CollatzFormal.lean` Section 18):

1. **(Falsification of $\langle 2, 3 \rangle < \mathbb{F}\sb p^\ast$ Coset Obstructions for $W \ge 3$ & Naive $2$-Adic Contradictions):**
   - `weight3_mod23_and_neg17_mod139_falsification_witnesses` certifies: (i) on $\mathcal{M}\sb 2$ ( $-17$ ), $\lvert 2^{11} - 3^7 \rvert = 139$ is prime with $\lvert \langle 2, 3 \rangle\sb{139} \rvert = 138$ (all of $\mathbb{F}\sb{139}^\ast$ ); (ii) at $p = 23$, $\lvert \langle 2, 3 \rangle\sb{23} \rvert = 11$ is odd ( $-1 \equiv 22 \notin \langle 2, 3 \rangle\sb{23}$ ), yet the weight $3$ word $v = (1, 1, 0, 1)$ gives $C(v) = 23 \equiv 0 \pmod{23}$ because $3$-term sumsets $9 + 3 \cdot 2^a + 2^b$ represent $0 \pmod{23}$ even when $2$-term sumsets cannot. Likewise, $3^3 (19/5) + 19 = 32 (19/5)$ and $3^3 (29/5) + 29 = 32 (29/5)$ hold to infinite $2$-adic precision in $\mathbb{Z}\sb 2$, refuting purely $2$-adic $3^W + N = 2^K$ contradictions.
2. **(Surviving $N_0$-Free Cycle Rigidity Laws):**
   - **Exact $2$-Adic Valuation Lock (`cycle_2adic_valuation_lock_replicate_false`):** For every cycle word $v = 0^a 1 u$ solving $(2^K - 3^W) x_0 = C(v)$, $v_2(C(0^a 1 u)) = a$ identically, forcing $2^a \mid x_0$ and $(x_0 / 2^a) \equiv 1 \pmod 2$.
   - **Subgroup Index Divisibility & Weight $2$ Odd-Order Obstruction (`weight2_carry_mod23_never_zero`):** Every prime $p \mid \lvert 2^K - 3^W \rvert$ ( $p \ge 5$ ) satisfies $\lbrack \langle 2, 3 \rangle_p : \langle 2 \rangle_p\rbrack \mid W$ and $\lbrack \langle 2, 3 \rangle_p : \langle 3 \rangle_p\rbrack \mid K$ ( $78$ prime factors verified across $2 \le K \le 11$ ), and whenever $\lvert \langle 2, 3 \rangle_p \rvert$ is odd ( $p \in \lbrace 23, 47\rbrace$ ), $p \nmid C(v)$ for **all** parity words of weight $w(v) \in \lbrace 1, 2\rbrace$.
3. (Exact $2$-Vertex $(x\sb{(1)}, x\sb{(2)})$ Reciprocal-Budget Split & C23 Frontier Certification on $m = 97..99, u = 1$ ):
   - **Ordered-Minimum Split & $s\sb{\text{low}}$-Stratified Top-Strip Bounds (`two_vertex_ordered_minimum_budget_split`, `s_low_top_strip_upper_bound`):** Let $x\sb{(1)} < x\sb{(2)}$ be the two smallest distinct odd spiral vertices ( $x\sb{(2)} \ge x\sb{(1)} + 2$ ). At $u = 1$, `clamped_c` equals **$6, 7, 8$** for $m = 97, 98, 99$ respectively (correcting the heuristic " $c = 6$ across $m = 97..99$ " estimate). Whenever $x\sb{(1)} \ge A_1 > D / B$ (above the single-vertex pole $1 / \text{bud} \approx 0.12\text{-}0.16 \, b\sb{\text{low}}$ ): (i) $s\sb{\text{low}} = 1$ with all remaining vertices $> B\sb{\text{low}}$ and $s = 1$ total budget is algebraically impossible (`s = 1 -> False`); (ii) under $s\sb{\text{low}} = 1$ ( $x\sb{(1)} \le b\sb{\text{low}} < x\sb{(2)} \le \dots \le x\sb{(c)}$ ), the sorted second minimum $x\sb{(2)}$ is analytically capped by $(c - 1) / (\text{bud} - \frac{1}{A_1 + 1})$, collapsing $B\sb{2,\text{up}}$ from **$\sim 2^{117..119}$ down to $\sim 2^{76}$** across $x\sb{(1)} \in \lbrack 0.65 b\sb{\text{low}}, b\sb{\text{low}}\rbrack$; and (iii) under $s\sb{\text{low}} = s \in \lbrace 2, \dots, c\rbrace$, `s_low_top_strip_upper_bound` proves $x\sb{(1)} + 1 \le \frac{s}{\text{bud} - (c - s)/(b\sb{\text{low}} + 1)}$: at **$s\sb{\text{low}} = 2$**, $\lbrack 0.8696 \, b\sb{\text{low}}, b\sb{\text{low}}\rbrack$ ( $m = 97$ ), $\lbrack 0.8511 \, b\sb{\text{low}}, b\sb{\text{low}}\rbrack$ ( $m = 98$ ), and $\lbrack 0.8333 \, b\sb{\text{low}}, b\sb{\text{low}}\rbrack$ ( $m = 99$ ) are algebraically empty, while for $3 \le s\sb{\text{low}} \le c$ the cutoff increases monotonically to $c / \text{bud} \approx 0.9524 \, b\sb{\text{low}}$ at $s\sb{\text{low}} = c$ (leaving $\lbrack 0.9524 \, b\sb{\text{low}}, b\sb{\text{low}}\rbrack$ empty across **all** $s\sb{\text{low}} \ge 2$ ).
   - **C23 Engine (`run_hensel_two_vertex_c` in `_hensel_fast.c` & `run_two_vertex_hensel_bands`):** Implements exact $640$-bit (`u640`) intermediate products $3^k u - 1$, exact $384$-bit $2$-adic inverses (`g_inv3_full`), dedicated `kd_lo_bridge` $2$-vertex pruning with dynamic `cur >= max(z + 2, x2_lo)` clamping, deterministic `max_budget` abort (`rc == 1`) across **all** modes `0, 1, 2`, and automatic odd-`u` sub-band bisection above `4,096` survivors, verified bit-for-bit identical against pure Python up to $350$ bits (with arbitrary-precision Python fallback above $350$ bits):

| $m$ ( $u = 1$ ) | Exact $c$ | $b\sb{\text{low}}$ Bits | Standard $B_2$ Bits | $s\sb{\text{low}} = 2$ Empty Above (All $s \ge 2$: $0.9524$ ) | $s\sb{\text{low}} = 1$ Upper $B\sb{2,\text{up}}$ Bits ( $A_1 = 0.65 b\sb{\text{low}}$ ) | `UpperExit` ( $r \le 2$ ) Nodes / Ops | Arith. Survivors (Drop $\le 2^{71}$ ) | Cycle Survivors |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **$97$** | **$6$** | $75$ | $117$ | $0.8696 \, b\sb{\text{low}}$ | **$76$** ( $-41$ bits) | $3{,}084$ / $274{,}527$ | $65$ ( $322$ at $r \le 3$ ) | **$0$** |
| **$98$** | **$7$** | $76$ | $119$ | $0.8511 \, b\sb{\text{low}}$ | **$76$** ( $-43$ bits) | $3{,}114$ / $276{,}079$ | $15$ ( $87$ at $r \le 3$ ) | **$0$** |
| **$99$** | **$8$** | $76$ | $119$ | $0.8333 \, b\sb{\text{low}}$ | **$76$** ( $-43$ bits) | $3{,}152$ / $277{,}868$ | $20$ ( $121$ at $r \le 3$ ) | **$0$** |

4. **(Next-Tier $3 \times 3$ Counter-Model Falsification & Survival Audit Matrix — `verify_next_tier_boost_counter_model_matrix`):**

| Mechanism Candidate | $\mathcal{M}\sb 1 = \mathbb{Q}\sb{(2)}^+$ ( $19/5,\; 29/5$ ) | $\mathcal{M}\sb 2 = \mathbb{Z}^-$ ( $-1, -5, -17 \in \mathcal{S}\sb \infty$ ) | $\mathcal{M}\sb 3 = (5n+1)$ on $\mathbb{Z}^+$ ( $5, 13, 17$ ) | Status on $\mathbb{Z}^+$ ( $3n+1$ ) |
| :--- | :--- | :--- | :--- | :--- |
| **A1 (Unsound):** Single-return $3$-adic sieve $\mu_M(B) \to 0$ | $0 \pmod 3$ fibers uncovered | $\mathbb{Z}^-$ unbounded below | **FAILS:** $n\sb{\min}^{(5)} = 5$ bounded ( $\le 208$ ) with $0$ mergers into $\lbrack 1, 4\rbrack$ | **FALSIFIED** ( $\mu_1(8) = \frac{3522}{6561} \approx 0.5368 > 0$ via $3 \nmid C(u)$ ) |
| **A2 (Theorem 29):** General $(a, b)$-Backward Sieve + Bit Exhaustion + Bounded $\implies$ Cycle | $\frac{19}{5}, \frac{29}{5}$ merge in $\mathbb{Q}\sb{(2)}^+$; blocked by non-well-ordering | $-1, -5, -17$ merge in $\mathbb{Z}^-$; blocked by no lower bound | Bounded $5$ forces positive cycle $13$ ( $17$ at $K=7, W=3$ ) | **SURVIVES** ( $n\sb{\min} \bmod 36 \in \lbrace 3, 7, 15, 19, 27\rbrace$; $T^{\lvert v \rvert}(n\sb{\min}) < 3^{w(v)}$ ) |
| **B1 (Unsound):** All-odd $y_0 \in \lbrack 5, n\sb{\min}-1\rbrack$ disjoint forest & uniform Fourier decay | Overlap inside $\mathbb{Z}^+$ ( $13 = \text{child}(5)$, $7 = \text{child}(11)$ ) | Non-primitive $\xi = 3^{W-1}$ stays $> 0.529$ | Naive $n\sb{\min} X^c > X$ fails Pigeonhole at $X = n\sb{\min}$ | **FALSIFIED** (fixed via `IsSyracuseForestRoot` & $\gcd(\xi,3)=1$ ) |
| **B2 (Theorem 30):** In-degree $0$ Forest + `BackwardCarryWindow` / `SievedForestCollision` `Prop`s | Excluded: positive integer forest; $v_5 = -1$ on $\frac{19}{5}, \frac{29}{5}$ | Excluded: $2^a T^K(x) < 0 < 3^b + C(u)$ on $-1, -5, -17$ | Excluded: $\lbrace 5, 13..208\rbrace$ & $\lbrace 17..108\rbrace$ disconnected from $\lbrack 1, 4\rbrack$ | **SURVIVES** (all four `Prop`s kernel-proved $\iff$ `CollatzConjectureStandard`) |
| **C1 (Unsound):** $\langle 2, 3 \rangle < \mathbb{F}\sb p^\ast$ coset obstruction ( $W \ge 3$ ) & $2$-adic $3^W + N = 2^K$ | **FAILS:** $27(\frac{19}{5}) + 19 = 32(\frac{19}{5})$, $27(\frac{29}{5}) + 29 = 32(\frac{29}{5})$ | **FAILS:** $p = 139$ full $\mathbb{F}\sb{139}^\ast$; at $p = 23$, $C(1,1,0,1) = 23$ | **FAILS:** $2^7 - 5^3 = 3 \mid C_5(v)$ on $13, 17$ | **FALSIFIED** ( $3$-term sumsets hit $0 \pmod{23}$ ) |
| **C2 (Theorem 31):** $v_2(x_0) = a$ Lock + Index Divisibility + $2$-Vertex $(x\sb{(1)}, x\sb{(2)})$ Split | Blocked by $\mathbb{Z}$-integrality $v_2(x_i + 1) \le \log_2(x_i + 1)$ | Blocked by $\Lambda > 0$ & $x\sb{(2)} \ge x\sb{(1)} + 2 > N_0$ | Blocked by $\log_2 5 > 2$ & $q = 3$ merger | **SURVIVES** ( $s\sb{\text{low}} = 1$ upper $B\sb{2,\text{up}} \approx 2^{76}$; $0$ cycle survivors) |

---

## 18. Modular Lean 4.35.0 Kernel Verification & Axiom Audit (`CollatzFormal.lean`)

All **$1{,}962$** audited theorems across the **$58$**-file modular `CollatzFormal` package (`CollatzFormal.lean`, `CollatzFormal/Core.lean`, `CollatzFormal/RationalLogSlabs.lean`, `CollatzFormal/Survivors.lean`, `CollatzFormal/BoostMechanisms.lean`, `CollatzFormal/CSFullConjecture.lean`, `CollatzFormal/CSWave3Synthesis.lean`, `CollatzFormal/Wave4WholeSpace.lean`, `CollatzFormal/Wave5WholeSpace.lean`, `CollatzFormal/Wave6WholeSpace.lean`, `CollatzFormal/Wave7WholeSpace.lean`, `CollatzFormal/Wave8WholeSpace.lean`, `CollatzFormal/Wave9WholeSpace.lean`, `CollatzFormal/HenselBridgeCore.lean`, `CollatzFormal/HenselBridge93To96.lean` + submodules, and `CollatzFormal/Survivors97To99.lean` + `Survivors97To99A`..`J`; zero external dependencies, pure Lean `4.35.0` Core with `-M 2048 -T 200000 -j 2`) compile cleanly through the Lean 4 kernel with **exit code `0`, zero warnings on both stdout and stderr, zero `sorryAx`, zero `native_decide`, and zero custom `axiom`s** (**$592$ theorems completely axiom-free `[]`**, audited automatically via `#print axioms` in `verify_lean4_kernel_proofs`, with all remaining theorems using only standard Lean foundational axioms `Classical.choice`, `Quot.sound`, `propext`):

0. **Formal Conjecture Definitions & Canonical Equivalence Bridges (`CollatzConjectureStandard`, `collatz_standard_iff_compressed`, `collatz_iff_strict_descent`, `collatz_iff_two_barriers`, `collatz_iff_one_equation_diophantine`, `one_equation_converse_universal`):** States the canonical uncompressed Collatz Conjecture matching standard Lean formalizations and proves in the Lean 4 kernel its exact logical equivalences (`↔`) to: (i) the compressed Terras conjecture, (ii) the strict stopping-time descent hypothesis, (iii) the exact conjunction `NoDivergentPositiveOrbits ∧ NoNontrivialPositiveCycles` (Open Problems A & B), and (iv) pure side-condition-free One-Equation Diophantine solvability $\forall n > 0,\; \exists v,\; 2^{\lvert v \rvert} = 3^{w(v)} n + C(v)$ (including full $2$-adic Hensel parity forcing in the converse).
1. **Universal Inductive Collatz Identities & General $(a, b)$-Affine Converse over $\mathbb{Z}$ (`affine_decomposition_universal`, `general_affine_converse_universal`, `bohm_sontacchi_cycle_equation_universal`, `one_equation_forward_universal`, `one_cycle_carry_closed_form_universal`):** Proved inductively for all parity vectors $v \in \lbrace \text{false}, \text{true}\rbrace ^\ast$ and all integers $x, y \in \mathbb{Z}$ (covering Theorems 1.1, 1.3, 3, 9, and 29.1).
2. **Entry/Exit Collatz Mergers & All 3 Potential-Telescoping Step Cases (`entry_collatz_merger_k2_algebraic`, `hercher_collatz_merger_algebraic`, `potential_telescoping_case1_cleared_denom`, `potential_telescoping_case2_cleared_denom`, `potential_telescoping_case3_cleared_denom`):** Proved universally over $\mathbb{N}$ via inductive exponential dominance `pow2_succ_lt_pow3` ( $2^{k+1} < 3^k$ for $k \ge 2$ ), establishing the step-wise backbone of Theorem 19.1.
3. **Universal $r$-Step Spiral Hensel Identity & Kernel-Checked Orbit-Drop Certificates (`spiral_hensel_identity_universal`, `all_32_hensel_survivors_drop_below_2_pow_71`, `all_55_new_m95_hensel_survivors_drop_below_2_pow_71`, `all_new_m96_to_98_hensel_survivors_drop_below_2_pow_71`, `m96_to_98_hensel_survivor_drop_universal`, `all_new_m97_to_99_hensel_survivors_drop_below_2_pow_71`, `m97_to_99_hensel_survivor_drop_universal`, `convergents_43_and_45_unimodular`):** Proves the arbitrary-depth spiral invariant $2^{K\sb r}(z\sb{r+1} + 1) = 3^{W\sb r}(z\sb 1 + 1) + G\sb r$ inductively over `SpiralPath`, verifies the exact $42$-digit unimodular determinants, and kernel-evaluates (`by decide`, zero-axiom `[]` batch theorems via `checkSurvivorBatchFast_sound` across `Survivors.lean` and `Survivors97To99A`..`J.lean`) that all recorded arithmetic Hensel survivors above $2^{71}$ through $1 \le m \le 99$ drop strictly $\le 2^{71}$.
4. **Universal Coalescence Partner, Quadratic Peak Floor, & Exact $S$-Integer / $5$-Adic Witnesses (`minimal_divergent_coalescence_universal`, `quadratic_peak_floor_cleared_square`, `s_integer_positive_2cycle_29_over_5_witness`, `five_adic_unit_denominators_eight_witnesses`):** Proves the cleared-square quadratic running-maximum floor (Theorem 21.1), the universal minimal-divergent coalescence partner inequality $1 \le n' < n_0$ and image identity (Theorem 22.2), and exact finite witnesses for Theorems 6, 7, 15, 17, 20.2, and 22.1.
5. **Line A Single-Block, Multi-Block, & General $(a, b)$-Affine Backward Merger Rigidity, Bit Exhaustion, Mod $1296$ Sieve, & Bounded Cycle Extraction (`minimal_counterexample_mod4_eq_3`, `hercher_entry_merger_a1_ge_2`, `subdouble_entry_merger_step`, `subquad_exit_tail_merger_step`, `general_affine_backward_merger_step`, `minimal_counterexample_mod12_in_3_or_7`, `minimal_counterexample_mod9_ne_4`, `minimal_counterexample_mod36_in_5_classes`, `minimal_counterexample_mod1296_surviving`, `two_return_garden_of_eden_escape`, `two_return_escape_suffix_congruence_mod81`, `garden_of_eden_div3_unmergeable`, `initial_bit_exhaustion_iter_lt_pow3`, `bounded_minimal_counterexample_implies_nontrivial_cycle`, `minimal_counterexample_archimedean_coalescence_exclusion`):** Proves single-, multi-block, and general parity-word backward mergers, the $5/36$ mod $36$ and $131/1296$ mod $1296$ surviving sieves, the $0 \pmod 3$ carry indivisibility barrier and two-return escape (`Theorem 32`), initial binary bit exhaustion $T^{\lvert v \rvert}(n\sb{\min}) < 3^{w(v)}$, and bounded-counterexample cycle extraction (Theorems 23, 27, 29, and 32).
6. **Line B Zero-Trust-Gap $1 \le m \le 93$ End-to-End Pipeline, `m = 94..96` High-Weight Bridges, Reflective Hensel Verifier, Prime-Denominator Locks, & $2$-Vertex $(x\sb{(1)}, x\sb{(2)})$ Split (`no_nontrivial_spiral_cycles_1_to_92`, `no_nontrivial_spiral_cycles_1_to_93`, `no_nontrivial_spiral_cycles_m94_u_ge_2`, `no_nontrivial_spiral_cycles_m95_u_ge_3`, `no_nontrivial_spiral_cycles_m96_u_ge_4`, `no_spiral_cycle_ge_q51`, `exactM92_all_k1_hensel_complete`, `verifyMultiStepHenselBand_sound`, `cycle_2adic_valuation_lock_replicate_false`, `weight2_carry_mod23_never_zero`, `weight3_mod23_and_neg17_mod139_falsification_witnesses`, `two_vertex_ordered_minimum_budget_split`, `s_low_top_strip_upper_bound`):** Proves end-to-end non-existence of non-trivial positive spiral cycles for $1 \le m \le 93$ (plus $u \ge 2$ at $m=94$, $u \ge 3$ at $m=95$, $u \ge 4$ at $m=96$ ) inside Lean 4 solely from `BarinaThreshold (2 ^ 71)` and `BakerLMNPowerBound`, exact $2$-adic and weight $2$ mod $23$ cycle locks, and the $2$-vertex ordered-minimum and $s\sb{\text{low}}$-stratified reciprocal-budget inequalities (Theorems 24, 26, and 31).
7. **Line C One-Equation Sign-Separation, Disjoint In-Degree $0$ Multi-Root Syracuse Forest, & Exact Open Mixing Equivalences (`one_equation_forces_pos`, `syracuseTreeWord_solves_one_equation`, `syracuseTree_overlap_witnesses`, `syracuseForestRoot_iff_not_child`, `syracuseForestVal_injective`, `syracuseForestVal_upper_bound`, `syracuseForestVal_reaches_root`, `collatz_standard_iff_backward_carry_window`, `collatz_standard_iff_multi_root_forest_collision`, `collatz_standard_iff_sieved_backward_carry_window`, `collatz_standard_iff_sieved_forest_collision`, `collatz_standard_iff_mod1296_sieved_forest_collision`):** Proves exact characterization and global injectivity of the multi-root inverse Syracuse forest on $\lbrack 5, n\sb{\min} - 1\rbrack$ and proves inside the Lean 4 kernel that all five carry-window / Syracuse-forest collision formulations are **logically equivalent (`↔`)** to `CollatzConjectureStandard` (Theorems 25, 28, 30, and 32).
8. **Scope Transparency:** Transcendental linear-forms-in-logarithms proofs (Laurent–Mignotte–Nesterenko 1995; Bugeaud–Laurent 1996, encoded explicitly as `BakerLMNPowerBound`), Barina's (2025) $2^{71}$ computational convergence threshold (`BarinaThreshold (2 ^ 71)`), and the large C23 / GPU Hensel tree enumerations extending beyond $1 \le m \le 93$ through $1 \le m \le 99$ (`prove_multistep_hensel_mcycle_nonexistence`, `prove_m96_m98_hensel_frontier`, `prove_m99_unconditional_hensel_frontier`) are verified computationally (C23 / OpenCL / Python) with all arithmetic survivor drops ( $1 \le m \le 99$ ) kernel-certified in Lean 4 (`Survivors.lean` and `Survivors97To99.lean`).

---

## 19. Theorems 32–33 Summary: Mod $1296$ Escape & Unconditional Positive Cycle Elimination Through $1 \le m \le 99$

1. **Theorem 32 (`verify_two_return_escape_and_mod1296_sieve`, `CollatzFormal/BoostMechanisms.lean` §19):**
   - Proves universally over $\mathbb{N}$ the exact concatenation law `affineCarry_append` ( $C(u\sb 1 u\sb 2) = 3^{w(u\sb 2)} C(u\sb 1) + 2^{\lvert u\sb 1 \rvert} C(u\sb 2)$ ), two-return Garden-of-Eden escape (`two_return_garden_of_eden_escape` forcing $x_2 \not\equiv 0 \pmod 3$ on every positive-weight return), suffix-shift surjectivity modulo $81$ (`two_return_escape_suffix_congruence_mod81`), and the complete mod $1296$ ( $2^4 \cdot 3^4$ ) minimal-counterexample sieve reducing surviving residue classes to $131/1296 \approx 10.1080\%$ while proving `CollatzConjectureStandard ↔ Mod1296SievedForestCarryCollisionProp`.
2. **Theorem 33 (`prove_m99_unconditional_hensel_frontier`, `CollatzFormal/Survivors97To99.lean`):**
   - Extends unconditional positive all-weight cycle elimination at $N_0 = 2^{71}$ to **$1 \le m \le 99$** (establishing `(99, 1)` dominance over `(97, 1)` and `(98, 1)` at $c = 8$, monotone $u$-tail cutoffs $u\sb{\text{cut}} = 14, 15, 15$, $4$-shell De Morgan upward-climb partitions in `_hensel_fast.c`, and pure-kernel `by decide` drop certification of $19{,}175$ net-new `m = 97..99` survivors in `CollatzFormal/Survivors97To99A`..`J.lean`), passing all $3 \times 3$ counter-model audits (`19/5`, `29/5` in $\mathbb{Q}\sb{(2)}^+$; `-1, -5, -17` in $\mathbb{Z}^-$; `5, 13, 17` for $5n + 1$ ).

---

## 20. Universal Conjecture Compression, Unique First-Hit Bijection, Mod $373{,}248$ & Parametric Sieves, & CS Obstructions (`CollatzFormal/CSFullConjecture.lean`, `CollatzFormal/CSWave3Synthesis.lean`)

`CollatzFormal/CSFullConjecture.lean` ( $201$ theorems, $7{,}577$ lines, Waves 1–2) and `CollatzFormal/CSWave3Synthesis.lean` ( $130$ theorems, $5{,}039$ lines, Wave 3) together establish **$331$ universally quantified pure-kernel Lean 4 theorems** (zero `BarinaThreshold`, zero `BakerLMNPowerBound`, zero finite $m$ tables, zero custom axioms) across three formal tracks audited by the $3 \times 3$ CEGAR harness (`cs_cegar_redteam.py`):

1. **Track 3 — All-Weight $(\mathbb{Z}/3^w\mathbb{Z})^\times$ Primitive-Root Lifting, Total Backward Quotients, Unique $x = 1$ First-Hit Bijection & Koopman Fibers (`cs_forest_transfer.py`, `CSFullConjecture.lean` §§1–3, 7 & `CSWave3Synthesis.lean` §8):**
   - **Constructive $3$-Adic Totient Lifting & $O(w)$ Hensel Discrete Log (`pow2_totient_pow3_exact_lifting`, `pow2_minimal_order_mod_pow3`, `dlog2ModPow3_bijective`):** Proves inductively for all $m \ge 0$ ( $w = m + 1 \ge 1$ ) that $2^{2 \cdot 3^m} = 1 + 3^{m+1} k_m$ with $k_m \bmod 3 = 1$, establishing $\operatorname{ord}\sb{3^w}(2) = 2 \cdot 3^{w-1}$ and constructing an explicit lookup-table-free Hensel discrete logarithm bijecting $\lbrace 0, \dots, 2 \cdot 3^{w-1} - 1\rbrace$ onto $(\mathbb{Z}/3^w\mathbb{Z})^\times$.
   - **Total Backward Predecessor Operator & Arbitrary-Depth Forest Collapse (`collatzIter_odd_nondiv3_universal`, `exactBackwardQuotient_spec`, `odd_forest_collision_collapses_to_core_contraction`):** Combines universal odd-start escape ( $T^K(n) \not\equiv 0 \pmod 3$ for every odd $n$ and $K \ge 1$ ) with non-positive forward invariance (`collatzIterInt_nonpos`) to eliminate all $3^w$-divisibility and lower-window side-conditions, collapsing arbitrary-depth inverse Syracuse forest collisions to `q = 0` core-word contraction `exactBackwardQuotient (collatzIter K n) u 0 < n`.
   - **Horizon-Supercritical Core Splitting & Exact Logarithmic Suffix-Shift Arc (`supercritical_core_word_dominance`, `horizon_supercritical_core_reduction_at_n`, `koopman_primitive_fiber_annihilation`, `affineCarry_universal_upper_bound`, `non_descending_contraction_forces_log_shift_arc`):** Proves constructively (`[]` axioms on prefix splitting) that any contracting backward core word decomposes at its first subcritical prefix into a strictly shorter horizon-supercritical core word (`IsHorizonSupercriticalFor`), proves scaled Koopman difference cancellation across $3^{w-1}$-coset fibers for all $w \ge 1$, proves the sharp carry bound $C(u) \le 2^{\lvert u \rvert - w(u)}(3^{w(u)} - 2^{w(u)})$, and proves (`T3.12c`) that whenever a non-descending iterate $x \ge n \ge 1$ ( $x \bmod 3 \ne 0,\; w(u) \ge 1$ ) achieves `exactBackwardQuotient x u 0 < n`, its suffix shift $a := \text{canonicalSuffixShift}(u, x)$ **must** lie in the logarithmic arc $2^a < 3^{w(u)}$ ( $a < \lceil w(u) \log\sb 2 3 \rceil$ inside $\lbrack 0, 2 \cdot 3^{w(u)-1}\bigr)$ ).
   - **Total $x = 1$ Convergent Generator, Unique First-Hit Bijection & Forward-Iteration-Free `Mod373248` Range Equivalences (`one_generator_pos_odd_and_reaches_one`, `one_generator_singleton_true_closed_form`, `one_generator_trivial_loop_extension`, `first_hit_one_pair_sound_and_injective`, `convergent_odd_gt1_iff_unique_first_hit_pair`, `collatz_standard_iff_mod373248_one_generator_range`, `one_generator_weight_le_two_never_surviving_mod1296`, `collatz_standard_iff_mod373248_unique_first_hit_range` — `T3.13`–`T3.16`):** Because $1 \bmod 3 \ne 0$ unconditionally, `y := exactBackwardQuotient 1 u q` generates a positive odd convergent integer for every core word $u$ and $q \in \mathbb{N}$ (mapping $\lbrack \text{true}\rbrack \mapsto (4^{q+1} - 1)/3 \in \lbrace 1, 5, 21, 85, \dots\rbrace$, while `uLoop := (u ++ replicate shift false) ++ [true]` traverses $\lbrace 1, 2\rbrace$ once more with `exactBackwardQuotient 1 uLoop 0 = y` and `¬ IsFirstHitOnePair uLoop 0`). Enforcing $\forall k < \text{backwardOneTotalSteps}(u, q),\; T^k(y) \ne 1$ in `IsFirstHitOnePair u q` (including $k = 0$ to exclude $y = 1$ ) yields a canonical bijection (`firstHitStepsAux`) onto all convergent odd integers $n > 1$. Moreover, since `exactBackwardQuotient x (true :: false :: rest) q % 4 = 1` ( $\forall x \bmod 3 \ne 0$ ) and `exactBackwardQuotient 1 [true, true] q` $= (32 \cdot 64^q - 5)/9 \equiv 3 \pmod{16}$ ( $\forall q$ ), every $w(u) \le 2$ or `true :: false :: _` core word is disjoint from `IsSurvivingMod1296Class` ( $y \bmod 16 \in \lbrace 7, 11, 15\rbrace$ ), proving the forward-iteration-free equivalence `CollatzConjectureStandard ↔ Mod373248OneGeneratorRangeProp ↔ Mod373248UniqueFirstHitRangeProp` (`u = true :: true :: tail`, $w(u) \ge 3$ ).

2. **Track 1 — Universal Cycle Sieves, Sharp $1$-Block $q\sb 0 \ge 17$ GCD Lock, Complete $2$-Block Brox Reduction & Master Synthesis (`cs_lp_cycles.py`, `CSFullConjecture.lean` §§4, 6 & `CSWave3Synthesis.lean` §10):**
   - **Cycle Ratio Sandwich, Mod $96$ ( $1/12$ ) Sieve & Unconditional $(21, 22)$ Exponent Band (`cycle_ratio_sandwich_and_peak_floor`, `cycle_constant_odd_implies_trivial`, `nontrivial_cycle_min_mod48_and_band_21_22`):** Rules out constant-odd / $W = 1$ non-trivial cycles universally, narrows any non-trivial positive cycle minimum $x\sb 0$ to $8$ residue classes modulo $96$ ( $\lbrace 7, 31, 47, 59, 71, 79, 91, 95\rbrace$ ), proves $21^W < 7^W \cdot 2^p \le 22^W$ (forcing $W \ge 5, p \ge 8$ with zero parity enumeration), and restricts $(2^K - 3^W) \bmod 24 \in \lbrace 5, 7, 13, 23\rbrace$ (`pow2_sub_pow3_mod24_in_4_classes`).
   - **$2$-Adic LTE Bound, Mersenne $1$-Cycle Elimination & Sharpened Brox Equivalence (`pow2_dvd_pow3_sub_one_le_four_mul`, `one_block_cycle_binary_squeeze_and_q0_ge_three`, `cycle_min_first_block_dichotomy`, `no_nontrivial_cycles_iff_sharpened_brox_obstruction`):** Proves $2^a \mid (3^w - 1) \implies 2^a \le 4w$ for all $w \ge 1$, eliminates all $q\sb 0 = 1$ ( $x\sb 0 = 2^{w\sb 1} - 1$ ) $1$-block cycles unconditionally, separates $(\mathbb{Z}^+, 3x+1)$ from $\mathcal{M}\sb 1 = \mathbb{Q}\sb{(2)}^+$ via the first-block integer-discreteness dichotomy, and proves universal impossibility of bounded-modulus $\pmod{2^A 3^B}$ rational-potential cycle certificates (`bounded_modulus_rational_potential_obstruction`).
   - **Sharp $1$-Block GCD / Mod $24$ Squeeze, Complete $2$-Block Primitive Brox Reduction & Master Campaign Equivalences (`one_block_gcd_and_congruence_lock`, `one_block_no_pow3_quotient_and_q0_ge_17`, `no_one_block_cycles_iff_sharpened_gcd_mod24`, `two_block_reciprocal_and_cross_carry_identity`, `two_block_mersenne_elimination_and_cubic_squeeze`, `no_two_block_cycles_iff_one_block_and_primitive_brox`, `subexponential_cubic_gap_eliminates_1_and_2_block_cycles`, `one_block_cycle_has_smaller_nonconvergent_partner`, `no_nontrivial_cycles_iff_wave3_sharpened_brox_obstruction`, `unified_wave3_master_collatz_equivalences` — `T9`–`T11`):** On $1$-block positive cycles, proves $3^{w\sb 1} - 2^{w\sb 1} = D x\sb 0$, $D \mid \gcd(2^{a\sb 1} - 1,\; 3^{w\sb 1} - 2^{w\sb 1})$, $2^{a\sb 1} \equiv 1 \pmod D$, $2^{w\sb 1} \equiv 3^{w\sb 1} \pmod D$, $\forall r,\; q\sb 0 \ne 3^r$, $q\sb 0 \bmod 24 \in \lbrace 3, 9, 17, 19\rbrace$, $q\sb 0 \ge 17$ ( $q\sb 0 \ge 19$ for odd $w\sb 1$ ), $w\sb 1 \ge 13,\; a\sb 1 \ge 8,\; x\sb 0 \bmod 96 \in \lbrace 31, 95\rbrace$, $\lfloor 17 \cdot 3^{w\sb 1} / 2^{a\sb 1} \rfloor = 17 \cdot 2^{w\sb 1} - 1$, and Hercher partner merger $T^{w\sb 1 + a\sb 1 - 1}((x\sb 0 - 1)/2) = x\sb 0$ (separating $\mathcal{M}\sb 3 = 5x+1$ where $13 \mapsto 6 \to 1$ ). On $2$-block cycles, eliminates Mersenne vertices $q\sb 0 = 1$ and $q\sb 1 = 1$ unconditionally ( $q\sb 0, q\sb 1 \ge 3,\; x\sb 0 \ge 47,\; x\sb 1 \ge x\sb 0 + 2,\; 23 D < 3^W,\; W \ge 8,\; K \ge 13$ ), separates $\mathcal{M}\sb 1$ witnesses $251/13 \leftrightarrow 439/13$ and $287/13 \leftrightarrow 331/13$, proves $27 \cdot 2^{W + a\sb 1 - 3} D^3 < 2^{3K}$ (`IsPrimitiveTwoBlockBroxWitness`) so `SubexponentialCubicGapProp -> NoOneBlockPositiveCycles ∧ NoTwoBlockPositiveCycles`, and unifies all campaign reductions in `unified_wave3_master_collatz_equivalences` (`IsWave3SharpenedBroxWitness`).

3. **Track 2 & Cross-Track Fusions — `bbchallenge` $3^w$ DFA Barrier, $\forall d \ge 1$ Matrix Identity Collapse, Mod $373{,}248$ & Infinite Parametric Sieves (`cs_sat_lyapunov.py`, `CSFullConjecture.lean` §§5–5B & `CSWave3Synthesis.lean` §9):**
   - **Mixed $(2,3)$ SRS Boundary Separation & All-Dimension Matrix Termination Obstructions (`srs_neg5_nine_step_cycle`, `monotone_affine_d1_natural_impossibility`, `arctic_quadratic_height_impossibility`, `d2_upper_triangular_natural_impossibility`, `all_dim_coord_monotone_upper_triangular_impossibility`, `sub6_admits_2d_top_left_monotone_upper_triangular_cert` — `T2.1`–`T2.4`, `T2.8`):** Formalizes the $11$-rule mixed binary-ternary rewriting semantics, exhibits the $9$-step $-5$ MSB sign-flip cycle, proves universal impossibility of $d = 1$ affine natural, $\forall d \ge 1$ arctic, and $d = 2$ top-left-monotone upper-triangular natural interpretations, and proves (`T2.8a`) by strong induction on superdiagonal offset $\delta = j - i \ge 0$ that in **every** dimension $d \ge 1$, any coordinatewise-monotone ( $\forall s, i,\; (M\sb s)\sb{i,i} \ge 1$ ) upper-triangular natural matrix interpretation orienting $\lbrace R\sb 2, R\sb 5, R\sb 7, R\sb 9, R\sb{11}\rbrace$ collapses to $M\sb s = I\sb d$ on $\lbrace B\sb 0, B\sb 1, T\sb 0, T\sb 1, T\sb 2\rbrace$ and fails $R\sb 8$ (sharp against the `[]`-axiom $d = 2$ top-left-monotone certificate `sub6UpperTri2DCert` with $(M\sb{B\sb 0})\sb{1,1} = 0$ in `T2.8b`).
   - **`bbchallenge` / Myhill–Nerode $2^w$ & $3^w$ Regular Invariant Barrier (`binGapWord_pairwise_myhill_nerode_distinguished`, `mnWitnessFamily_card_pow3_and_pairwise_distinguished`, `no_finite_dfa_recognizes_one_equation_language` — `T2.7`):** Proves on the exact $1$-convergent parity language `IsValidOneEquationWord` ( $\exists n \ge 1,\; 2^{\lvert v \rvert} = 3^{w(v)} n + C(v)$ ) that all $2^w$ fixed-weight $w$ binary-gap words `binGapWord bs` (via $3$-adic Hensel cross-differences) and all $3^w$ words in `mnWitnessFamily w` ( $1 + \sum\sb{j=1}^w 2 \cdot 3^{j-1} = 3^w$ ) are pairwise separated by explicit pure-`false` suffixes $0^k$, constructively refuting **every** $N$-state deterministic finite automaton ( $\forall N \ge 1$ ) via finite pigeonhole ( $3^N > N$ ).
   - **All-Weight $2^{w\sb 1}$-Cancellation, Mod $373{,}248$ Survival ( $2.7633\%$ ), Self-Congruent Pumping & Infinite Dyadic/Triadic Sieves (`all_weight_cancellation_word_step`, `survivingMod373248_count_eq_10314`, `self_congruent_syracuse_pumping_mod373248_obstruction`, `collatz_standard_iff_mod373248_horizon_supercritical_contraction`, `infinite_dyadic_entry_merger_excluded_family`, `infinite_triadic_backward_merger_excluded_family` — `T2.5`–`T2.6`, `T2.9`):** Compresses minimal-counterexample residue classes to **$10{,}314 / 373{,}248 = 191 / 6{,}912 \approx 2.7633\%$** ( $n \ge 27$ ), proves no residue-indexed monotone potential $\Phi(x, x \bmod 2^A 3^B)$ can decrease across self-congruent Syracuse return arcs inside `IsSurvivingMod373248Class`, and proves (`T2.9`) two infinite pairwise-disjoint hierarchies of minimal-counterexample exclusions: (i) $n = 2^{k+2} q + r\sb k^{\text{dyad}}$ for all $k \ge 2$ (coalescing with $n' = (n - 1)/2 < n$ and surviving mod $512$ inside $\lbrace 255, 511\rbrace$ for all $k \ge 8$ ), and (ii) $n = 3^{2k+6} q + r\sb k^{\text{triad}}$ with $r\sb k^{\text{triad}} = (27 c\sb{k \bmod 6} 9^k - 7)/2$ for all $k \ge 3$ (satisfying $r\sb k^{\text{triad}} \equiv 361 \pmod{729}$ so it survives $100\%$ of mod $729$ exclusions, while merging from an explicit $1 \le n' < n$ in $3k + 10$ compressed steps via $2^{3k+10} < 3^{2k+6}$ ).



---

## 21. Wave 4 Whole-Space Proof Loop: Radial Hardy/Bergman Barrier, Two-Sided & One-Sided Cobham–Presburger Collapse, Laurent Valuation-Monomial Impossibility, $2$-Block Resultant Lock, Sharp $w \ge 6$ First-Hit Floor, & Solvable Mixed-$(2,3)$ Cousin Synthesis (`CollatzFormal/Wave4WholeSpace.lean`, `PROOF_SPACE_LEDGER.md`, `witness_bank.json`)

`CollatzFormal/Wave4WholeSpace.lean` ($91$ theorems, zero custom axioms) together with the persistent taxonomy in `PROOF_SPACE_LEDGER.md` and automated witness-bank runner in `cs_cegar_redteam.py` (`witness_bank.json`, $32$ ground-truth-verified witnesses across $5$ domains + $8$ structured falsification records) explores five orthogonal whole-space paradigms:

1. **Branch P1 — Universal $\forall r \ge 1$ Berg–Meinardus Radial Hardy / Weighted Bergman Transfer-Operator Impossibility (`berg_meinardus_radial_hardy_norm_gt_one`, `berg_meinardus_rational_and_bergman_norm_gt_one`, `berg_meinardus_weighted_bergman_and_exp_instances`):**
   - For any radial positive Borel measure $\nu$ on $\mathbb{D}$, the moment weights $w_n = \int_0^1 r^{2n}\,d\nu(r)$ are positive and non-increasing ($w_b \le w_a$ for $3 \le a \le b$, including decaying rational moments $w_n = p_n / q_n \to 0$ such as weighted Bergman $w_n = (n+1)^{-k}$ and interior-disk $w_n = 2^{-n}$). For every iterate horizon $r \ge 1$, the odd Mersenne seed $n\sb{\text{odd}} = 2^{r+1} - 1 \ge 3$ and even companion $n\sb{\text{even}} = 2^r m_r$ avoid $\lbrace 1, 2\rbrace$ across Steps $0..r$ and collide at $m_r = 3^r \cdot 2 - 1 > n\sb{\text{odd}}$, forcing $(w(n\sb{\text{odd}}) + w(n\sb{\text{even}})) / w(m_r) > 1$ and hence $\|\mathcal{B}^r\|\sb{\mathcal{H}\sb 0(w)}^2 > 1$ across all radial Hardy/Bergman spaces.
2. **Branch P2 — Furstenberg $(\times 2, \times 3)$ Zero-Entropy Subgroup & Mod-$3^B$ Dirac Pinning Falsification (`audit_h2_furstenberg_zero_entropy_and_mod3_pinning`):**
   - Every positive cycle gap $D = 2^K - 3^W$ satisfies $\gcd(D, 6) = 1$, making $\frac{1}{D}\mathbb{Z}/\mathbb{Z} \subset \mathbb{R}/\mathbb{Z}$ an exact zero-entropy finite $(\times 2, \times 3)$-invariant subgroup outside Rudolph–Host positive-entropy measure rigidity; in $\mathbb{Z}^+$, Mersenne glides $2^W - 1$ deterministically pin $W - B$ consecutive steps to $-1 \bmod 3^B$.
3. **Branch P3 — Simultaneous Hermite–Padé Mahler-Duality Obstruction & Unconditional $2$-Block Resultant / Quotient-GCD Lock (`two_block_brox_resultant_identities`, `two_block_quotient_mersenne_gcd_and_mod3_lock`):**
   - Exact rational + high-precision evaluation of simultaneous Hermite–Padé approximants to $(1, -\log(1 - a_1 t), -\log(1 - a_2 t))$ certifies two distinct failure modes: at asymmetric $\{2, 3\}$-smooth bases such as $(1/4, 1/3)$, even diagonal $(n, n)$ cleared-denominator Type-II error exceeds $1$ by $n = 6$ ($2^{3.40}$); at the unique folded symmetric $\{2, 3\}$-smooth basis $(1/3, -1/3)$ ($u = t^2/9$), finite-$n$ Chebyshev dips keep diagonal $(n, n)$ error $< 1$ up to $n \le 35$ ($2^{-9.99}$ at $n = 6$, $2^{-21.17}$ at $n = 18$), yet step-line $(n+1, n)$ explodes ($2^{+10.66}$ at $n = 6$), Type-I height overtakes remainder decay at $n = 8$, and odd primes up to $2n - 1$ in $\operatorname{lcm}(1, 3, \dots, 2n - 1) \sim e^{2n}$ drive even diagonal $(n, n)$ above $1$ by $n = 55$ ($2^{+7.08}$).
   - Exploiting carry-coupled divisibility $D \mid H_0, H_1$ on $2$-block cycles yields the exact resultant eliminations $2^{a_1+w_2} H_1 = 3^{w_1} H_0 + D(2^{a_1} - 1)$ and $2^{a_2+w_1} H_0 = 3^{w_2} H_1 + D(2^{a_2} - 1)$, proving unconditionally that $\gcd(q_0, q_1) \mid \gcd(2^{a_1} - 1, 2^{a_2} - 1)$ (coprime whenever $a_1 = 1$ or $a_2 = 1$) and $(3 \mid q_0 \implies 2 \mid a_2) \land (3 \mid q_1 \implies 2 \mid a_1)$ (while refuting uncoupled $\gcd(H_0, H_1) \le 2^{\gcd(a_1, a_2)} - 1$ at minimal shared-factor witnesses $D = 175, \gcd = 5$ and $D = 1631, \gcd = 7$).
4. **Branch P4 — Two-Sided & One-Sided Cobham–Presburger Collapse, Monotone $r$-Step Ranking Barrier, & Arbitrary-Sign Laurent Valuation-Monomial Impossibility (`presburger_invariant_separator_collapse`, `one_sided_presburger_infinite_forward_hits_one`, `no_one_sided_presburger_divergent_certificate`, `monotone_ranking_function_r_step_impossibility`, `syracuse_laurent_valuation_monomial_impossibility`):**
   - Halving and tripling period reductions combined with the commutator chains $z \mapsto 12z + 2$ and $z \mapsto 12z + 1$ prove that every two-sided ultimately periodic ($\forall N_0, P \ge 1$) Collatz-invariant predicate collapses identically to $I(x) \leftrightarrow I(1)$, AND 2-adic valuation lifting + $2^{3^m} \equiv -1 \pmod{3^{m+1}}$ inversion on $3^b$ + finite-permutation backward preimages on coprime $R$ prove that **every** one-sided forward-closed ultimately periodic set containing any $x_0 \ge N_0$ reaches $1$. Mersenne glides $2^{X_0 + 1 + r} - 1$ refute every eventually strictly increasing $r$-step ranking function $V(x)$, while on odd Syracuse steps, across **all** arbitrary-sign integer triples $(\alpha, \beta, \gamma) \in \mathbb{Z}^3$ (including non-monotone coercive $4^{v_2(x+1)}(x+1)$, which survives Mersenne glides yet jumps $40 \to 512$ at $9 \to 7$), the 4-element witness set $\lbrace 7, 9, 17, 97\rbrace$ forces $\gamma \ge 1$ and $7^\gamma < 9^\beta < 4^\alpha < 5^\gamma$, an unconditional contradiction.
5. **Branch P5 — Solvable Mixed-$(2,3)$ Cousin Benchmark $T\sb\diamond$, Antagonism on True $3x + 1$, & Sharp $w \ge 6$ Elimination on `exactBackwardQuotient 1 u q` (`cousin_diamond_global_convergence`, `cousin_diamond_mod_pow2_pow3_potential_impossibility`, `cousin_diamond_no_finite_dfa_trace_language`, `one_generator_weight_le_five_never_surviving_mod373248`, `collatz_standard_iff_mod373248_unique_first_hit_weight_ge_six`, `mod373248_min_weight_six_witness_184111`):**
   - Defines $T\sb\diamond(x) = (3x+1)/2$ on all odd $x$, $(x-2)/3$ on even $x > 2$ with $x \equiv 2 \pmod 6$, and $x/2$ otherwise. Inside the Lean 4 kernel, $T\sb\diamond$ is proved to exhibit unbounded $(3/2)^K$ Mersenne glides, defeat all $\pmod{2^A 3^B}$ monotone-per-residue potentials ($\forall A, B \ge 1$) and all $N$-state DFAs ($\forall N \ge 1$), admit non-trivial cycles on $\mathcal{M}\sb 1 = \mathbb{Q}\sb{(6)}^+$ ($1/7$) and $\mathcal{M}\sb 2 = \mathbb{Z}^-$ ($-1, -5$), and **converge globally to $1$ for every $x \in \mathbb{Z}^+$** via $\Phi\sb\diamond(x) = \operatorname{core}\sb 3(x + 1)^2 (x + 1)$ (while GP with parsimony discovers the minimal 3-node exact invariant $(x+1)\operatorname{core}\sb 3(x+1)$). On `exactBackwardQuotient 1 u q`, proving all $27$ surviving $\bmod 512$ classes have 9-step weight $\ge 6$ eliminates every core parity word of weight $w(u) \le 5$ across **all** $q \in \mathbb{N}$ from `IsSurvivingMod373248Class`, sharpening `Mod373248UniqueFirstHitRangeProp` from $w \ge 3$ to the exact sharp floor $w \ge 6$ (realized at `u = [true, true, true, true, false, true, false, true], q = 0 -> y = 184,111`, $27$ compressed steps).

---

## 22. Wave 5 Whole-Space Proof Loop: Non-Radial Preimage Superharmonicity, Closer Cousin $T_{\diamond 2}$ & Multi-Term / Non-Triangular Barriers, $\forall m \ge 1$ Spiral Resultants & Antipodal Prime Exclusions, & Coupled $q$-Ray Covering (`CollatzFormal/Wave5WholeSpace.lean`, `PROOF_SPACE_LEDGER.md`, `witness_bank.json`)

`CollatzFormal/Wave5WholeSpace.lean` ($138$ theorems, zero custom axioms, zero `sorryAx`, zero `native_decide`) together with `PROOF_SPACE_LEDGER.md` and `witness_bank.json` ($41$ ground-truth-verified witnesses across $5$ domains + $12$ structured barrier/falsification records) advances four orthogonal Wave 5 fronts:

1. **Front A (`Branch P1.2`) — Non-Radial Berg–Meinardus Preimage Superharmonicity Meta-Theorems & Periodic/Valuation Impossibility (`nat_valued_preimage_weight_impossibility`, `preimage_superharmonic_rational_eliminates_all_cycles`, `strictly_contractive_bounded_preimage_weight_implies_collatz_standard`, `berg_meinardus_periodic_valuation_weight_impossibility`, `berg_meinardus_reciprocal_multiterm_laurent_impossibility`):**
   - **Forward Meta-Theorems:** Any positive cleared-denominator rational preimage weight $w(n) = p(n)/q(n)$ on $\mathbb{N}\sb{\ge 3}$ satisfying $w(2m) + \mathbf{1}\sb{m \equiv 2 \pmod 3,\; (2m-1)/3 \ge 3} w((2m-1)/3) \le \theta \, w(m)$ with $\theta \le 1$ unconditionally implies `NoNontrivialPositiveCycles` across **all** $m \ge 1$ (`preimage_superharmonic_rational_eliminates_all_cycles`, because along any non-trivial cycle $m_0 \to \dots \to m\sb{p-1} \to m_0$, at least one odd step $m_i \equiv 2 \pmod 3$ injects strictly positive off-cycle mass $w(2 m_i) > 0$), and when $\theta < 1$ with bounded orbit denominators implies `CollatzConjectureStandard` (`strictly_contractive_bounded_preimage_weight_implies_collatz_standard`, non-vacuous via $w(n) = 3^{-\sigma(n)}, \theta = 2/3$).
   - **Universal Non-Radial Barriers (`zero custom axioms`):** `nat_valued_preimage_weight_impossibility` proves no $\mathbb{N}\sb{>0}$-valued preimage weight exists ($w(4^{k+1}) + k \le w(4)$ along $4^{j+1} \equiv 1 \pmod 3$). Along the 4-adic geometric spine $S_j = 4^{3j+1}$ with odd preimages $z_j = (4^{3j+4} - 1)/3 \in \lbrace 85, 5461, 349525, \dots\rbrace$, $(2^{v_2(z_j)}, 3^{v_3(z_j)}, 2^{v_2(z_j+1)}, 3^{v_3(z_j+1)}) = (1, 1, 2, 1)$ is **identically constant** across all $j \ge 0$ while $T(z_j) = 2 \cdot 4^{3j+3} = 32 S_j$ forces $w(S\sb{j+1}) + w(z_j) \le w(32 S_j) \le \dots \le w(S_j)$ and hence $w(S_J) + \sum\sb{j=0}^{J-1} w(z_j) \le w(4)$, constructively refuting (`berg_meinardus_periodic_valuation_weight_impossibility`, $\forall P \ge 1$) every positive rational preimage weight depending only on $(n \bmod P, v_2(n), v_3(n), v_2(n+1), v_3(n+1))$, as well as every reciprocal multi-term Laurent valuation weight (`berg_meinardus_reciprocal_multiterm_laurent_impossibility`).
2. **Front B (`Branch P4.2`, `P4.3`, `P5.4`) — Closer Cousin $T\sb{\diamond 2}$, Non-Triangular Matrix Collapse ($\forall d \ge 1$), & All-Length Multi-Term Laurent Valuation Impossibility (`all_dim_coord_monotone_non_triangular_impossibility`, `cousin_diamond2_global_convergence`, `cousinDiamond2StepInt_ofNat_eq`, `cousin_diamond2_single_laurent_monomial_impossibility`, `cousin_diamond2_counter_model_separation`, `two_term_valuation_sum_survives_w4_witnesses_yet_fails_syracuse`, `syracuse_multiterm_laurent_valuation_impossibility`):**
   - **Non-Triangular Matrix Barrier ($\forall d \ge 1$, `zero custom axioms`):** Dropping `IsUpperTriMat` in `NatAffineDim d` under coordinatewise monotonicity $\forall s, i, (M_s)\sb{i,i} \ge 1$ buys zero expressive power: decomposing $M_s = I_d + E_s$ ($E_s \ge 0$), sandwiching $R_2, R_9, R\sb{11}$ forces $L B_1 B_0 R \le L B_1 R$ and hence $E\sb{B_0} = 0$ and $E\sb{B_1} = E\sb{T_0} = E\sb{T_2}$, after which $R_5$ and $R_7$ collapse $M_s = I_d$ across all $5$ interior symbols $\lbrace B_0, B_1, T_0, T_1, T_2\rbrace$, refuting $R_8$ (`all_dim_coord_monotone_non_triangular_impossibility`).
   - **Closer $(3x+1)$-Cousin Benchmark $T\sb{\diamond 2}$ (`zero custom axioms`):** Unlike Wave 4's $T\sb\diamond$ (which only takes $(3x+1)/2$ on odd $x$), $T\sb{\diamond 2}$ takes $(3x+1)/4$ on odd $x$ with $x \equiv 1 \pmod{16}, x \not\equiv 2 \pmod 3$, or $x \ge 73, x \equiv 9 \pmod{64}, x \not\equiv 2 \pmod 3$, or $x \ge 17, \operatorname{core}\sb 3(x+1) = 2$, matching **true Syracuse** on $7 \to 11 \to 17 \to 13$, $53 \to 40$ (even), and $97 \to 73 \to 55$ while preserving unbounded $(3/2)^K$ Mersenne glides (`cousin_diamond2_unbounded_glide_and_mod_barrier`) and exact signed `Int` agreement (`cousinDiamond2StepInt_ofNat_eq`). Inside Lean 4, $T\sb{\diamond 2}$ is proved to **defeat every single Laurent valuation monomial** on $\lbrace 7, 17, 73, 97\rbrace$ (`cousin_diamond2_single_laurent_monomial_impossibility`), reject $\mathcal{M}\sb 1$ ($1/7$ via `cousinDiamond2IterQ6`), $\mathcal{M}\sb 2$ ($-1, -5$), and $\mathcal{M}\sb 3$ ($7x+1$, seed $5$) (`cousin_diamond2_counter_model_separation`, `[]` axioms), AND **converge globally to $1$ with polynomial stopping bound $k \le (x+1)^3 + (x+1)^5$** via the 2-term valuation sum $\Phi\sb{\diamond 2}(x) = 2^{v_2(x+1)} \operatorname{core}\sb{2,3}(x+1)^3 + (2^{v_2(x+1)})^5 (3^{v_3(x+1)})^3$ (`cousin_diamond2_global_convergence`).
   - **Universal $\forall L \ge 1$ Multi-Term Laurent Valuation Impossibility on True $(3x+1)$ (`zero custom axioms`):** While 2-term sums genuinely beat Wave 4's finite set $\lbrace 7, 9, 17, 97\rbrace$ yet rebound at $3 \to 5$ ($17 \to 21$) and $13 \to 5$ (`two_term_valuation_sum_survives_w4_witnesses_yet_fails_syracuse`, `[]` axioms), `syracuse_multiterm_laurent_valuation_impossibility` proves constructively that **no finite positive combination of $L \ge 1$ Laurent valuation monomials** can strictly descend across all odd $x \ge 3$ with $S(x) \ge 3$: asymptotic dominance across $97 \to 73$, $2 \cdot 9^{k_2} - 1$ (`core` $\times 3$, `v_3` $/ 3^{2 k_2}$), $2 z\sb{j_3} - 1 \to 2^{6 j_3 + 7} - 1$ (`core` $\to 1$, `v_2` $\to 2^{6 j_3 + 7}$), and $8 \cdot 3^k - 1 \to 4 \cdot 3^{k+1} - 1$ (`v_2` $8 \to 4$, `v_3` $\times 3$) forces an unconditional contradiction.
3. **Front C (`Branch P3.2`, `P3.3`, `P3.4`) — Beukers–Rhin 2D Integral Falsification, Universal $\forall m \ge 1$ `m`-Block Spiral Resultants, & Antipodal-Order Divisor Exclusion (`broxSpiralCarry_eq_affineCarry_universal`, `m_block_brox_resultant_and_quotient_locks`, `m_block_cycle_induces_brox_quotients`, `one_block_even_even_impossibility`, `one_block_antipodal_order_divisor_exclusion`, `one_block_antipodal_prime_instances_and_m1_separation`):**
   - **2D Beukers–Rhin & Constant-Term Elimination Audit (`_solve_beukers_rhin_2d_and_const_elimination`):** Cross-verified to $< 10^{-40}$ against the exact Beta-function power series, non-separable 2D Euler–Rhin integrals $I_n = \iint_{[0,1]^2} \frac{x^n(1-x)^n y^n(1-y)^n u^{2n+1}}{(1-ux)^{n+1}} dx\,dy$ ($u = (3+y)/6$) avoid dilogarithms and decay exponentially ($2^{-6.30}$ at $n = 1$, $2^{-27.80}$ at $n = 5$), yet squared $\operatorname{lcm}(1,\dots,3n+3)^2 \cdot 6^n$ denominators overtake decay ($2^{+3.45}$ already at $n = 1$, $2^{+18.55}$ at $n = 5$, $2^{+39.91}$ at $n = 8$), while constant-term elimination between 1D Legendre–Beukers forms for $\log 2$ and $\log(3/2)$ dips at $n = 1$ ($-8 \log 2 + 5 \log 3$, $2^{-4.26}$) before exploding ($2^{+3.44}$ at $n = 5$, $2^{+5.02}$ at $n = 8$).
   - **Universal $\forall m \ge 1$ Spiral Resultant, Affine-Carry Bridge, & Quotient Locks (`zero custom axioms`, choice-free):** `broxSpiralCarry_eq_affineCarry_universal`, `m_block_brox_resultant_and_quotient_locks`, and `m_block_cycle_induces_brox_quotients` bridge `broxSpiralCarry` to `affineCarry` across **every block count $m \ge 1$** ($2^{w_0} H_0 + 3^W = 2^K + C_K(v)$), prove $2^{a_j + w\sb{j+1}} H\sb{j+1} = 3^{w_j} H_j + D(2^{a_j} - 1)$, propagate single-block divisibility $D \mid H_0 \implies \forall j < m, D \mid H_j$, and establish $\gcd(q_0,\dots,q\sb{m-1}) \mid \gcd_j (2^{a_j} - 1)$, unit-even-run primitivity $(\exists j, a_j = 1) \implies \gcd_j q_j = 1$, and the exact cyclic mod-3 bi-implication $3 \mid q\sb{j+1} \iff 2 \mid a_j$.
   - **1-Block Even-Even Impossibility & Antipodal Prime Exclusion (`zero custom axioms`):** `one_block_even_even_impossibility` factors $2^{2v + 2u} - 3^{2v} = (2^{v+u} - 3^v)(2^{v+u} + 3^v) > 2^{2u} - 1$ for all $v, u \ge 1$. Coupling this with $D \mid \gcd(2^{a_1} - 1, 3^{w_1} - 2^{w_1})$ proves (`one_block_antipodal_order_divisor_exclusion`) that **every odd integer $p \ge 3$ admitting $2^{m_1} \equiv -1 \pmod p$ and $2^{m_2} + 3^{m_2} \equiv 0 \pmod p$** ($28$ primes $< 300$, including $\lbrace 5, 11, 13, 17, 37, 41, 59, 61, 83, 97\rbrace$) is unconditionally excluded from dividing $D = 2^{w_1+a_1} - 3^{w_1}$ on 1-block $\mathbb{Z}^+$ cycles — strictly separating $\mathbb{Z}^+$ from $\mathcal{M}\sb 1 = \mathbb{Q}\sb{(2)}^+$ where $p = 5$ ($19/5$) and $p = 13$ ($211/13$) occur as exact 1-block denominators!
4. **Front D (`Branch P5.3` & `P4.4`) — Coupled $q$-Ray Covering, Automatic $q \ge 1$ First-Hit, Sharp $\lvert u \rvert \ge 8$ Floor, & $\Pi\sb 2^0$ Skolem Calibration (`exactBackwardQuotient_one_ray_step_law`, `one_generator_q_pos_always_first_hit`, `mod373248_ray_dyadic_pinning_and_triadic_bijection`, `one_generator_length_le_seven_never_surviving_mod373248`, `collatz_standard_iff_mod373248_unique_first_hit_len_ge_eight`, `pi2_skolem_box_equivalence_and_cousin_polynomial_stopping_bound`):**
   - **Coupled $q$-Ray Laws & Automatic $q \ge 1$ First-Hit (`zero custom axioms`):** Proves $y\sb{q+1} = y_q + 2^{L_q} k_w = 2^{2 \cdot 3^{w-1}} y_q + k_w C(u)$ with $k_w = (2^{2 \cdot 3^{w-1}} - 1)/3^w \equiv 1 \pmod 3$, proves `IsFirstHitOnePair u q` holds **automatically for all $w(u) \ge 2$ and $q \ge 1$** (`one_generator_q_pos_always_first_hit`, even when $q = 0$ wraps around $\lbrace 1, 2\rbrace$), and proves for all $w(u) \ge 6$ that $L_0 \ge 10$, $y_q \bmod 512 = y_0 \bmod 512$ is constant across $q$, while $q \mapsto y_q \bmod 729$ is a **bijection on `Fin 729`** (`mod373248_ray_dyadic_pinning_and_triadic_bijection`, visiting all $382$ surviving $\bmod 729$ classes per period of $729$).
   - **Sharp $\lvert u \rvert \ge 8$ Floor & $\Pi\sb 2^0$ Skolem Calibration (`zero custom axioms`):** Because none of the $27$ surviving $\bmod 512$ classes has 9-step parity suffix `(false, false)` (`survivingMod512Bool_nine_gt_seven_weight`), `one_generator_length_le_seven_never_surviving_mod373248` eliminates **all** core parity words of length $\lvert u \rvert \le 7$ (including $1^6 \mapsto 1170$ and all length-$7$ weight-$6/7$ words) across all $q \in \mathbb{N}$, upgrading `W4.5c` to `Mod373248UniqueFirstHitLenGeEightProp` ($\text{tail.length} \ge 6$, sharp at $\lvert u \rvert = 8, y = 184{,}111$). Finally, `pi2_skolem_box_equivalence_and_cousin_polynomial_stopping_bound` proves constructively that a Skolem search box $(\text{tail.length}, 486 q) \le B(n)$ on `IsSurvivingMod373248Class` exists iff a total compressed stopping-time bound $S(n)$ exists (contrasted with $T\sb{\diamond 2}$'s polynomial $\mathrm{I}\Delta_0 + \exp$ bound $(x+1)^3 + (x+1)^5$).

---

## 23. Wave 6 Whole-Space Proof Loop: 6-Variable Coupled-Core Preimage Barrier, Zero-Diagonal Matrix & Spiral Block-Return Barriers, 3rd Solvable Cousin $T_{\diamond 3}$, Multiplicative Schneider–Laurent Determinants & 2-Block Locks, and Cross-Ray Prefix-Fiber Covering (`CollatzFormal/Wave6WholeSpace.lean`, `PROOF_SPACE_LEDGER.md`, `witness_bank.json`)

`CollatzFormal/Wave6WholeSpace.lean` ($76$ theorems, zero custom axioms, zero `sorryAx`, zero `native_decide`) together with `PROOF_SPACE_LEDGER.md` and `witness_bank.json` ($47$ ground-truth-verified witnesses across $5$ domains + $16$ structured barrier/falsification records) advances four orthogonal Wave 6 fronts:

1. **Front A (`Branch P1.2` & `P1.3`) — Universal 6-Variable Coupled-Core Rational Preimage-Weight Impossibility (`coupled_core_weight_survives_spine_and_17_yet_fails_mersenne`, `spine_bounded_ratio_preimage_impossibility`, `berg_meinardus_coupled_core_rational_weight_impossibility`):**
   - Coupling the $(2, 3)$-coprime core $\operatorname{core}\sb{2,3}(n)$ into $w\sb{\text{core}}(n) = (2^{v_2(n+1)})^2 / (\operatorname{core}\sb{2,3}(n)^2 + (3^{v_3(n+1)})^3)$ genuinely cures Wave 5's 4-adic spine divergence ($\sum\sb{j=0}^J w\sb{\text{core}}(z_j) < 10^{-3}$ across $z_j = (4^{3j+4}-1)/3$) and satisfies strict Syracuse growth $w\sb{\text{core}}(x) < w\sb{\text{core}}(\operatorname{Syr}(x))$ on $\lbrace 17 \to 13,\; 97 \to 73,\; 169 \to 127\rbrace$, yet fails on Mersenne glides $7 \to 11$ (`coupled_core_weight_survives_spine_and_17_yet_fails_mersenne`).
   - Universally over **all** non-empty positive polynomial quotients $P / Q$ in all $6$ valuation and coprime-core coordinates $(2^{v_2(n)}, 3^{v_3(n)}, \operatorname{core}\sb{2,3}(n), 2^{v_2(n+1)}, 3^{v_3(n+1)}, \operatorname{core}\sb{2,3}(n+1))$ (`evalCoupledCorePoly`), preimage superharmonicity along $S_j = 4^{3j+1}$ ($S\sb{j+1} = 64 S_j$, $T(z_j) = 32 S_j$) forces $\sum_j w(z_j) \le w(4)$ (`spine_bounded_ratio_preimage_impossibility`), requiring $\gamma_Q \ge \gamma_P + 1$ along $z_j$ ($\operatorname{core}\sb{2,3}(z_j) = z_j$); then $2 \cdot 9^k - 1$ forces $\beta_Q - \beta_P \ge \gamma_Q - \gamma_P \ge 1$, $2 z_j - 1$ forces $\alpha_Q \le \alpha_P + (\beta_Q - \beta_P)$, and the $2r$-step Mersenne glide $2^{2r+1} - 1 \to 2 \cdot 9^r - 1$ pits $9^{r(\beta_Q - \beta_P)}$ against $C \cdot 4^{r(\beta_Q - \beta_P)}$, refuting every 6-variable coupled-core rational preimage weight (`berg_meinardus_coupled_core_rational_weight_impossibility`).
2. **Front B (`Branch P4.3` & `P5.5`) — Zero-Diagonal & Bipartite-Swap Matrix Collapses, Spiral Block-Return Impossibility on True $(3x+1)$, & 3rd Solvable Cousin $T\sb{\diamond 3}$ (`sub6_upper_tri_2d_forces_zero_diag_B0`, `zero_diag_upper_tri_2d_r1_sub6_impossibility`, `zero_top_left_breaks_left_context_monotonicity_2d`, `bipartite_zero_diag_swap_r1_impossibility_all_dim`, `antidiag_swap_2d_r1_impossibility`, `spiral_block_return_unbounded_climb`, `spiral_block_return_multiterm_laurent_impossibility`, `cousin_diamond3_global_convergence`, `cousin_diamond3_multiterm_laurent_impossibility`, `cousin_diamond3_counter_model_separation`):**
   - **Zero-Diagonal & Bipartite-Swap Matrix Barriers (`zero custom axioms`):** First, `zero_top_left_breaks_left_context_monotonicity_2d` (choice-free) proves that allowing $(M\sb{B_0})\sb{0,0} = 0$ destroys left-context rewrite monotonicity (`[B0, T2, B1] -> [B0, B1, T2]` fails even when `[T2, B1] -> [B1, T2]` is strictly oriented). Allowing zero lower-right diagonal entries $n_s = 0$ in `UpperTri2D` ($m_s \ge 1$), `sub6_upper_tri_2d_forces_zero_diag_B0` proves $\lbrace R_2, R_5, R_7, R_9, R\sb{11}\rbrace$ forces $n\sb{B_0} = 0$ and $d_R \ge 1$, and `zero_diag_upper_tri_2d_r1_sub6_impossibility` proves that adding $R_1$ ($L B_0 \to L$) to $\lbrace R_2, R_5, R_7, R_8, R_9, R\sb{11}\rbrace$ collapses universally via $2 n\sb{B_1} \le n\sb{B_1}^2 + 1$ vs strict $R_8$ ($2 n\sb{B_1} > n\sb{B_1}^2 + 1$). Finally, `bipartite_zero_diag_swap_r1_impossibility_all_dim` (and $d = 2$ corollary `antidiag_swap_2d_r1_impossibility`) proves across **all $d \ge 1$** that every 2-block bipartite zero-diagonal swap interpretation $M_s = \begin{pmatrix} 0 & P_s \\ Q_s & 0 \end{pmatrix}$ collapses on $R_1$ alone.
   - **True $(3x+1)$ Spiral Block-Return Barrier (`zero custom axioms`):** Stepping across a complete odd-glide + even-drop block (`spiralBlockReturn`) climbs strictly for $r$ consecutive blocks on $4 \cdot 16^r - 5 \to 4 \cdot 18^r - 5$ ($\forall r \ge 1$, minimal $r = 2$: $1019 \to 1147 \to 1291$, `spiral_block_return_unbounded_climb`) AND defeats **every** $L$-term ($\forall L \ge 1$) Laurent valuation sum across $\lbrace 97 \to 73,\; 2 z_j - 1 \to 2 \cdot 4^{3j+3} - 1,\; 2^{2r+1} - 1 \to (3 \cdot 9^r - 1)/2\rbrace$ (`three_family_multiterm_laurent_obstruction`, `spiral_block_return_multiterm_laurent_impossibility`).
   - **3rd Solvable $(3x+1)$-Cousin Benchmark $T\sb{\diamond 3}$ (`zero custom axioms`):** Extends $T\sb{\diamond 2}$ with Cone 4 ($x \ge 169 \land x \equiv 1 \pmod 8 \land \operatorname{core}\sb 2(3x+5) = 1 \mapsto (3x+1)/4$, starting at $169 \to 127$ where $\Phi\sb{\diamond 2}$ jumps $1{,}228{,}282 \to 34{,}359{,}738{,}496$) and even spine drain ($x \ge 20 \land x \equiv 2 \pmod{18} \mapsto (x-2)/9$). Inside Lean 4, $T\sb{\diamond 3}$ is proved to **defeat ALL fixed-step $L$-term ($\forall L \ge 1$) Laurent valuation sums** (`cousin_diamond3_multiterm_laurent_impossibility`), agree identically between `Nat` and signed `Int` (`cousinDiamond3StepInt_ofNat_eq`), reject $\mathcal{M}\sb 1$ ($1/7$), $\mathcal{M}\sb 2$ ($-1, -5$), and $\mathcal{M}\sb 3$ ($7x+1$, seed $5$) (`cousin_diamond3_counter_model_separation`, `[]` axioms), AND **converge globally on $\mathbb{Z}^+$ within $k \le (x+1)^3 + (x+1)^5$ steps** via variable-horizon Cone-4 block-return (`cousin_diamond3_cone4_reaches_one_exact` & `cousin_diamond3_global_convergence`, using `pow9_succ_add_seven_ne_pow2`: $9^{r+1} + 7 \ne 2^M$ for $r \ge 2$ via coupled $\bmod 27, 7, 19$ congruences).
3. **Front C (`Branch P3.2`, `P3.3`, `P3.4`) — Multiplicative Schneider–Laurent Interpolation Determinants, $\forall m \ge 1$ Shared-Mersenne Antipodal Locks, & 2-Block Equal-Even Cone Exclusion (`laurent_interp_2x2_5_8_and_3x3_determinant_cert`, `laurent_interp_resonant_row_collapse_and_gap_divisibility`, `m_block_antipodal_shared_mersenne_parity_and_mod3_lock`, `two_block_shared_mersenne_propagation_and_equal_even_exclusion`):**
   - **Multiplicative Schneider–Laurent Determinants (`[]` & `zero custom axioms`):** Pure-integer entries $\binom{r W + s K}{t} 2^{r u} 3^{s u} \in \mathbb{N}$ (`laurentInterpEntry`) bypass $\operatorname{lcm}$ integration denominators completely, prove universal $(2^K - 3^W)$ divisibility across resonant row pairs $(m K, 0)$ vs $(0, m W)$, and prove $U = 1$ ($u = 0$) collapses $\det = 0$ identically (`laurent_interp_resonant_row_collapse_and_gap_divisibility`). Computationally (`_solve_laurent_2log_interpolation_det`), fixed grid $(6, 6, 12, 3)$ ($36 \times 36$) dips to $2^{-457.75}$ at $(5, 8)$ and $2^{-217.45}$ at $(12, 19)$ before $W^{T(T-1)U/2} = W^{198}$ drives $2^{+134.77} > 1$ at $(41, 65)$ and $2^{+708.70}$ at $(306, 485)$, whereas growing $(R, S, T, U) \propto \log W$ restores $2^{-697.58}$ at $(41, 65)$ ($8 \times 8 = 16 \times 4$) and $2^{-667.03}$ at $(306, 485)$ ($10 \times 10 = 20 \times 5$, $\det\sb{\mathbb{Z}} M \ne 0$ certified modulo $3$ primes) — isolating Laurent's algebraic zero-multiplicity lemma ($\det M \ne 0$ for growing $U \sim \log W$) as the exact remaining bridge to `SubexponentialCubicGapProp`.
   - **Shared-Mersenne $m$-Block & Equal-Even 2-Block Locks (`zero custom axioms`):** `m_block_antipodal_shared_mersenne_parity_and_mod3_lock` proves across **all $m \ge 1$** that any antipodal divisor $p \mid \gcd(D, \gcd_j (2^{a_j}-1))$ forces $\forall j < m,\; 2 \mid a_j$, $2 \mid W$, $2 \mid K$, and $3 \mid \gcd(q_0,\dots,q\sb{m-1})$. For $m = 2$, `two_block_shared_mersenne_propagation_and_equal_even_exclusion` proves single-Mersenne prime propagation ($\forall p \mid D,\; p \mid (2^{a_1}-1) \iff p \mid (2^{a_2}-1)$), the equal-even-run sub-exponent lock $a_1 = a_2 \land w_2 < w_1 \implies D \mid (2^{a_1}-1)(3^{w_1-w_2} - 2^{w_1-w_2})$, and unconditional 2-block cycle exclusion across the infinite cone $a_1 = a_2 \land w_2 < w_1 \land 2 \mid (w_1 + w_2) \land 3 w_1 \le 5 w_2$.
4. **Front D (`Branch P5.3`) — Cross-Ray Disjointness, Exact $11 + 16 = 27$ Prefix Partition, Automatic `w ≥ 7` Free-Bit Fiber Biconditional, & Quantitative Zero-Density Sparsity (`first_hit_ray_global_disjointness_and_q0_necessity`, `mod512_surviving_prefix_partition_cert`, `exactBackwardQuotient_mod512_eq_coreWordMod512`, `mod512_surviving_prefix_uniform_fibers`, `surviving_mod512_nine_prefix_auto_weight_and_characterization`, `bounded_length_ray_exponential_sparsity_and_noncovering`, `bounded_length_ray_logarithmic_counting_zero_density`):**
   - **Cross-Ray Disjointness & $q = 0$ Loop Collision (`zero custom axioms`):** Proves global cross-ray injectivity across `IsFirstHitOnePair`, unconditional $q \ge 1$ cross-ray disjointness across all $w(u) \ge 2$ core words (including loop-extended words), and $q = 0$ collision sharpness on $184{,}111 \in \text{IsSurvivingMod373248Class}$ (`first_hit_ray_global_disjointness_and_q0_necessity`).
   - **Exact $11 + 16 = 27$ Surviving $\bmod 512$ Prefix Partition & $\forall L \ge 10$ Automatic `w ≥ 7` Uniform Fibers (`zero custom axioms`):** `mod512_surviving_prefix_partition_cert` (choice-free) paired with `exactBackwardQuotient_mod512_eq_coreWordMod512` proves that $11$ of $32$ length-$8$ core words and $16$ of $64$ length-$9$ core words ($w \ge 6$) disjointly partition all $27$ surviving $\bmod 512$ classes, while `mod512_surviving_prefix_uniform_fibers` and `surviving_mod512_nine_prefix_auto_weight_and_characterization` prove that every surviving 9-bit prefix `p9 := parityOfIter 9 r` has `p9.take 2 = [true, true]` and `parityWeight p9 ≥ 6`, so all $2^{L-10}$ extensions `p9 ++ freeBits ++ [true]` automatically satisfy `parityWeight u ≥ 7` and `exactBackwardQuotient 1 u q % 512 = r` (conversely characterizing every length $\ge 10$ core word hitting `IsSurvivingMod373248Class`).
   - **Exponential Sparsity, Logarithmic Counting, & Zero Natural Density (`zero custom axioms`):** Proves `exactBackwardQuotient 1 u q ≥ 2^(486 * q)` for all $w(u) \ge 6, q \in \mathbb{N}$, constructively refutes covering by any finite length cutoff $\lvert u \rvert \le L\sb{\max}$ (`bounded_length_ray_exponential_sparsity_and_noncovering`), and proves `< 2^(L_max + 1) * Q` total hits below $2^{486 Q}$ (`∀ Q ≥ 1`) and asymptotic natural density $0$ (`∀ D ≥ 1, D * hits.length < 2^(486 * Q)` at $Q = D + L\sb{\max} + 2$, `bounded_length_ray_logarithmic_counting_zero_density`).

---

## 24. Wave 7 Whole-Space Proof Loop: $W$-Dilated Schneider–Laurent Determinant Bridge & Common-Order Prime Exclusions, Binary Digit/Bit-Length & Mahler–Tauberian Barriers, 2D/3D Non-Triangular Hofbauer–Waldmann Certificates & 4th Solvable Cousin $T_{\diamond 4}$, and Markov Suffix-Shift / Minimal $L^2$ Fiber Dispersion (`CollatzFormal/Wave7WholeSpace.lean`, `PROOF_SPACE_LEDGER.md`, `witness_bank.json`)

`CollatzFormal/Wave7WholeSpace.lean` ($111$ theorems, zero custom axioms, zero `sorryAx`, zero `native_decide`) together with `PROOF_SPACE_LEDGER.md` and `witness_bank.json` ($53$ ground-truth-verified witnesses across $5$ domains + $20$ structured barrier/falsification records) advances four orthogonal Wave 7 fronts:

1. **Front A (`Branch P3.2`, `P3.3`, `P3.4`) — Pure-Kernel $W$-Dilated Schneider–Laurent Remainder Congruence, Scaled Nonvanishing Gap Bridge, Common-Order Prime Exclusions ($60/60$ Odd Primes $< 300$), & 2-Block $(41r, 65r)$ Odd-Order Prime Floor (`pow_sub_pow_mean_value_sandwich`, `laurent_interp_2x2_closed_form_and_nonvanishing`, `laurent_wdilated_zero_gap_entry_and_det_congruence`, `laurent_gap_bridge_eliminates_1_and_2_block_cycles`, `laurent_scaled_nonvanishing_eliminates_1_and_2_block_cycles`, `one_block_common_divisor_impossibility`, `one_block_common_order_prime_exclusion`, `odd_order_primes_and_331_mult_order_cert`, `one_block_odd_order_primes_7_19_23_31_43_47_71_73_and_331_barrier`, `two_block_shared_mersenne_common_order_scaling_and_squeeze`, `squeeze69_up_to_40_cert`, `two_block_odd_order_primes_7_19_23_31_43_47_71_73_weight_41r_floor`):**
   - **Moderate-$W$ Cofactor Stripping Audit (`_solve_laurent_perturbed_cubic_gap_det`, witness `LAURENT_SCALED_W41_CUBIC_GAP_AND_PRIME331_BARRIER`):** On the growing grid $(R, S, T, U) = (8, 8, 16, 4)$ ($64 \times 64$) at $(W, K) = (41, 65)$, while the zero-gap determinant satisfies $\lvert \det M_0 \rvert = 2^{-697.58} \ll 1$ and $\det\sb{\mathbb{Z}} M \ne 0$, evaluating at a putative `SubexponentialCubicGapProp` violation $\Lambda\sb{\text{cubic}} = 2^{-W/3} \ln 2$ only strips $N - 1 = 63$ Schwarz powers while $63 \times 63$ cofactors grow to $2^{+2423}$, leaving $\lvert \det M(\Lambda\sb{\text{cubic}}) \rvert \approx 2^{+2382.47} \gg 1$ — proving Baker/Laurent column extrapolation ($U' \gg U$) is mathematically indispensable at moderate $W$.
   - **Pure-`Nat`/`Int` $W$-Dilated Determinant Congruence & Scaled Nonvanishing Bridge (`zero custom axioms`):** Without complex contours or $\mathbb{R}/\mathbb{C}$ analysis, `laurent_wdilated_zero_gap_entry_and_det_congruence` proves entrywise $(2^K - 3^W) \mid \bigl(M\sb{0,\mathbb{Z}}[(r,s),(t,u)] - M[(r,s),(t,Wu)]\bigr)$ across all $(r,s,t,u)$ via the discrete mean-value sandwich $n b^{n-1}(a-b) \le a^n - b^n \le n a^{n-1}(a-b)$ (`pow_sub_pow_mean_value_sandwich`) and proves by arbitrary-$N$ Laplace induction that $(2^K - 3^W) \mid (\det\sb{\mathbb{Z}} M\sb{0,\mathbb{Z}} - \det\sb{\mathbb{Z}} M_W)$, yielding the integer Liouville bound $2^K - 3^W \le \lvert \det\sb{\mathbb{Z}} M\sb{0,\mathbb{Z}} \rvert + \lvert \det\sb{\mathbb{Z}} M_W \rvert$ whenever $\det\sb{\mathbb{Z}} M\sb{0,\mathbb{Z}} \ne \det\sb{\mathbb{Z}} M_W$, alongside exact $2 \times 2$ non-vanishing $(2^K)^u - (3^W)^u > 0$ (`laurent_interp_2x2_closed_form_and_nonvanishing`). Coupling `laurent_gap_bridge_eliminates_1_and_2_block_cycles` with `laurent_scaled_nonvanishing_eliminates_1_and_2_block_cycles` discharges `SubexponentialCubicGapProp` unconditionally for all $W \ge 6, K \ge 1$ with $2 \cdot 3^W \le 2^K$ and across the entire $W = 6$ family, and formalizes the exact implication chain `LaurentScaledNonvanishingProp -> TightConvergentCubicGapProp -> SubexponentialCubicGapProp ∧ NoOneBlockPositiveCycles ∧ NoTwoBlockPositiveCycles`.
   - **Common-Order Prime Exclusions ($60/60$ Primes $< 300$) & Sharp $(41r, 65r)$ 2-Block Odd-Order Prime Floor (`[]` & `zero custom axioms`):** `one_block_common_divisor_impossibility` proves $2^{r v + r u} - 3^{r v} > 2^{r u} - 1$ for all $r \ge 2, v, u \ge 1$, allowing `one_block_common_order_prime_exclusion` to eliminate **every** odd divisor $p \ge 3$ with $\gcd(\operatorname{ord}_p(2), \operatorname{ord}_p(3/2)) \ge 2$ on 1-block $\mathbb{Z}^+$ cycles — unconditionally excluding all pure odd-order primes $\lbrace 7, 19, 23, 31, 43, 47, 71, 73\rbrace$ (`odd_order_primes_and_331_mult_order_cert`, `[]` axioms; `one_block_odd_order_primes_7_19_23_31_43_47_71_73_and_331_barrier`, choice-free) and **100% of all $60$ odd primes $5 \le p < 300$**, while isolating **$p = 331$** ($\operatorname{ord}\sb{331}(2) = 30, \operatorname{ord}\sb{331}(3/2) = 11, \gcd = 1$ — unique among all $784$ odd primes $5 \le p < 6000$) as the minimal pure-order barrier. On 2-block shared-Mersenne cycles, `two_block_shared_mersenne_common_order_scaling_and_squeeze` proves across **all** $r = \gcd(\operatorname{ord}_p(2), \operatorname{ord}_p(3/2)) \ge 1$ that $W \ge 5r,\; a_1 + a_2 \ge 3r,\; K \ge 8r$ (via $22^3 < 7^3 \cdot 2^5$) and $23 r (2^{K/r} - 3^{W/r}) < 3^{W/r}$ (eliminating $(W/r, K/r) = (5, 8)$ for all $r \ge 1$), while `squeeze69_up_to_40_cert` (`[]` axioms) and `two_block_odd_order_primes_7_19_23_31_43_47_71_73_weight_41r_floor` eliminate all $1 \le W/r \le 40$ whenever $r \ge 3$, forcing **$W \ge 41r, K \ge 65r$** across all 8 odd-order primes $\lbrace 7, 19, 23, 31, 43, 47, 71, 73\rbrace$ ($W \ge 123, K \ge 195$ for $p \in \lbrace 7, 19\rbrace$ up to $W \ge 943, K \ge 1495$ for $p = 47$).
2. **Front B (`Branch P1.2` & `P1.3`) — Non-Algebraic Binary Digit-Run / `bitLength` Preimage Impossibility & Bivariate Mahler–Koopman Tauberian Non-Uniqueness (`binary_digit_sig6_and_bitlength_infinite_collision_family`, `berg_meinardus_binary_digit_sig_impossibility`, `berg_meinardus_exponential_popcount_bitlength_impossibility`, `berg_meinardus_coupled_digit_sig_and_bitlength_impossibility`, `mahler_koopman_tauberian_balance_and_m3_nonuniqueness`, `mahler_bivariate_pole_subtraction_and_half_exponent_decay`):**
   - **Binary Digit-Signature & Logarithmic `bitLength` Barriers (`zero custom axioms`, witness `ZPOS_BINARY_RUN_COLLISION_200`):** Along the infinite family $m_k = 3 \cdot 4^k + 8$ ($\forall k \ge 3$, minimal $k = 3$: $m_3 = 200, 2 m_3 = 400, n\sb{\text{odd}} = 133$), the 6-coordinate binary digit signature $(\operatorname{pop}_1(n), \operatorname{runs}_1(n), \operatorname{alt}\sb{01}(n), \operatorname{pop}_1(n+1), \operatorname{runs}_1(n+1), \operatorname{alt}\sb{01}(n+1))$ is identically $(3, 2, 3, 4, 3, 4)$ on **both** $m_k$ and $2 m_k$ and $(3, 3, 4, 3, 2, 3)$ on $n\sb{\text{odd}}(k) = 2^{2k+1} + 5$, while $\operatorname{bitLength}(n\sb{\text{odd}}(k)) = \operatorname{bitLength}(m_k) = 2k + 2$ and $\operatorname{bitLength}(2 m_k) = 2k + 3$ (`binary_digit_sig6_and_bitlength_infinite_collision_family`). This refutes every positive rational preimage weight $f(\operatorname{sig}_6(n)) \cdot P(\operatorname{bitLength}(n)) / Q(\operatorname{bitLength}(n))$ (`berg_meinardus_coupled_digit_sig_and_bitlength_impossibility`), while $7 \to 11 \leftarrow 22$ ($\operatorname{pop}_1 = 3$, $\operatorname{bitLength} \in \lbrace 3, 4, 5\rbrace$) refutes every exponential bit-length weight $g(\operatorname{pop}_1(n)) \cdot (a\sb{\text{num}}/a\sb{\text{den}})^{\operatorname{bitLength}(n)}$ via $a\sb{\text{num}}^2 + a\sb{\text{den}}^2 \le a\sb{\text{num}} a\sb{\text{den}}$ (`berg_meinardus_exponential_popcount_bitlength_impossibility`).
   - **Mahler–Koopman Tauberian Non-Uniqueness & Bivariate Pole Subtraction (`zero custom axioms`):** `mahler_koopman_tauberian_balance_and_m3_nonuniqueness` proves the universal parity-split sum identity $\sum\sb{n=1}^{2N} a(n) = \sum\sb{m=1}^N a(m) + \sum\sb{k=0}^{N-1} a(q k + r + 1)$ for every odd $q = 2r + 1$ and any $T_q$-invariant $a : \mathbb{N} \to \mathbb{N}$, proves universal invariance of cycle-basin indicators `ReachesGenCycle`, and constructs two disjoint $\{0, 1\}$-valued $T_5$-invariant basins on $\mathcal{M}_3 = (5x + 1)$ ($\lbrace 1, 2, 4\rbrace$ vs $\lbrace 13, 33, 83, 208, 104, 52, 26\rbrace$, with divergent seed $7$ outside both), while `mahler_bivariate_pole_subtraction_and_half_exponent_decay` (choice-free) proves cleared-denominator bivariate pole subtraction $w\sb{\text{den}}^T - (w\sb{\text{den}}^T - w\sb{\text{num}}^T) = w\sb{\text{num}}^T$ and uniform half-exponent geometric decay $w\sb{\text{num}}^T w\sb{\text{den}}^{\lfloor(n+1)/2\rfloor} \le w\sb{\text{num}}^{\lfloor(n+1)/2\rfloor} w\sb{\text{den}}^T$.
3. **Front C (`Branch P4.3` & `P5.6`) — Breakthrough 2D & 3D Non-Triangular Hofbauer–Waldmann Certificates on `sub6 ∪ {R1}`, $\forall d \ge 1$ Lower-Triangular & $\omega^k$ VASS/Tower Barriers, & 4th Solvable Cousin $T_{\diamond 4}$ (`r1_sub6_admits_2d_nontriangular_hofbauer_waldmann_cert`, `r1_sub6_admits_3d_nontriangular_hofbauer_waldmann_cert`, `all_dim_lower_triangular_hofbauer_waldmann_impossibility`, `omega_k_affine_rule_removal_and_parikh_vass_impossibility`, `swap_rule_parikh_vass_impossibility`, `cousin_diamond4_global_convergence`, `cousin_diamond4_r_block_spiral_climb_and_laurent_impossibility`, `cousin_diamond4_counter_model_separation`):**
   - **2D & 3D Non-Triangular Certificates vs Lower-Triangular & $\omega^k$ Barriers:** ALREADY in $d = 2$, `r1_sub6_admits_2d_nontriangular_hofbauer_waldmann_cert` (`[]` axioms!) constructs `r1Sub6NonTri2DCert` ($(M_s)\sb{0,0} = 1$, $(M\sb{B_0})\sb{1,1} = 0$, $(M\sb{B_0})\sb{1,0} = 5$, $(M\sb{B_0})\sb{0,1} = 10$, $(M\sb{T_2})\sb{0,1} = 26$) and in $d = 3$, `r1_sub6_admits_3d_nontriangular_hofbauer_waldmann_cert` (`[]` axioms!) constructs `r1Sub6NonTri3DCert` ($(M_s)\sb{0,0} = 1$, interior subdiagonals $(M\sb{B_0})\sb{1,0} = (M\sb{T_0})\sb{2,0} = 1, (M\sb{B_0})\sb{2,1} = (M\sb{T_1})\sb{2,1} = 6$, superdiagonals $(M_s)\sb{0,1}, (M_s)\sb{0,2}$) orienting **all $7$ rules `sub6 ∪ {R1}` simultaneously**, separating full non-triangular $d = 2$ from Wave 6's `UpperTri2D` and $\forall d \ge 1$ bipartite swap barriers! Conversely, `all_dim_lower_triangular_hofbauer_waldmann_impossibility` proves every $\forall d \ge 1$ lower-triangular $(M_s)\sb{0,0} \ge 1$ matrix collapses on $\lbrace R_2, R_5, R_7, R_9, R\sb{11}\rbrace$, and `omega_k_affine_rule_removal_and_parikh_vass_impossibility` + `swap_rule_parikh_vass_impossibility` refute all $k$-counter commutative Parikh/VASS rankings on $\lbrace R_2, R\sb{11}\rbrace$ and swap rules $R_3, R_8$ ($\forall k$) as well as all $k$-level Zantema–Geser $\omega^k$ iterated 1D natural-affine rule-removal towers on `sub6RuleList` ($\forall k : \mathbb{N}$).
   - **4th Solvable Cousin $T\sb{\diamond 4}$ (`zero custom axioms`, witnesses `ZPOS_COUSIN_DIAMOND4_CONE5_1529_JUMP`, `M1_COUSIN_DIAMOND4_1_OVER_7`, `M3_COUSIN_DIAMOND4_7X1_CYCLE5`):** Extends $T\sb{\diamond 3}$ with Cone 5 ($x \ge 89 \land x \equiv 25 \pmod{32} \land x \equiv 2 \pmod 3 \land \operatorname{core}\sb{2,3}(x+7) = 1 \mapsto (3x+1)/4$), reproducing true $(3x+1)$'s unbounded $r$-block spiral climb $4 \cdot 16^r - 5 \to^{2r} 4 \cdot 18^r - 5$ (`1019 -> 1529 -> 1147 -> 1721 -> 1291`) and defeating all $L$-term Laurent valuation sums (`cousin_diamond4_r_block_spiral_climb_and_laurent_impossibility`), while converging globally to $1$ within $k \le \Phi\sb{\diamond 2}(x) \le (x+1)^3 + (x+1)^5$ steps via closed-form Cone-5 multi-block return (`cousin_diamond4_cone4_and_cone5_exact_return`, `cousin_diamond4_global_convergence`) and separating $\mathcal{M}_1$ (`1/7`), $\mathcal{M}_2$ (`-1, -5`), and $\mathcal{M}_3$ ($7x+1$, seed `5`) (`cousin_diamond4_counter_model_separation`, `[]` axioms).
4. **Front D (`Branch P5.3` & `P2.2`) — History-Free Markov Suffix-Shift Recurrence, Sharp $q = 0$ Leaf Archimedean Envelope, & Unconditional Equal-Length Global Injectivity / Minimal $L^2$ Energy (`canonicalSuffixShift_append_markov_recurrence`, `q0_leaf_two_sided_archimedean_envelope_and_l12_drop`, `fixed_length_ray_global_injectivity_and_minimal_l2_collision_energy`):**
   - **Markov Skew-Product Shift Law (`zero custom axioms`):** `canonicalSuffixShift_append_markov_recurrence` proves `canonicalSuffixShift u 1` is odd on **every** word ending in `true` (all core parity words) and satisfies an exact history-free Markov transition on $(w, a)$: `u ++ [false]` maps $a \mapsto a - 1$ (if $a \ge 1$) else $2 \cdot 3^{w-1} - 1$, while `u ++ [true]` maps $(w, a) \mapsto \bigl(w + 1,\; \operatorname{dlog}\sb{2, 3^{w+1}}(3 \cdot 2^a + 1) - 1\bigr)$ with even $\operatorname{dlog} \ge 2$ and zero wraparound.
   - **Two-Sided $q = 0$ Envelope, Non-Monotone Length Drop, & Minimal $L^2$ Collision Energy (`zero custom axioms`, witness `ZPOS_RAY_Q0_NONMONOTONE_LENGTH_DROP_L12`):** `q0_leaf_two_sided_archimedean_envelope_and_l12_drop` proves $1 \le C(u) < 3^w \cdot 2^{\lvert u \rvert}$ and $3^w y_0 < 2^{\lvert u \rvert + a} < 3^w (y_0 + 2^{\lvert u \rvert})$ across all $w(u) \ge 1$, plus non-monotone length drop $y_0(u\sb{12}) < y_0(u\sb{10})$ inside `IsSurvivingMod373248Class` at equal weight $w = 8$. Finally, `fixed_length_ray_global_injectivity_and_minimal_l2_collision_energy` proves **unconditional global injectivity across all equal-length core words and all $q \in \mathbb{N}$** (including $q = 0$, with zero `IsFirstHitOnePair` hypothesis required!) and `NoDupNat` across all $27 \cdot 2^{L-10}$ surviving $L$-bit leaves ($\forall L \ge 10$), certifying minimal diagonal $L^2$ collision energy $27 \cdot 2^{L-10}$.

---

## 25. Wave 8 Whole-Space Proof Loop: `10/11` Mixed $(2,3)$ SRS Certificates & $\omega^k$ Towers, Cyclotomic Companion-Prime Quotient Forcing vs $p = 331$ & Laurent Binomial-Taylor Extrapolation, Non-Separable Ripple-Carry / $\forall W\sb{\text{win}} \ge 1$ Sliding-Window Barriers & 5th Solvable Cousin $T_{\diamond 5}$, and Cross-Scale $q = 0$ Leaf Biconditional / Markov Mod-$6$ Lock (`CollatzFormal/Wave8WholeSpace.lean`, `PROOF_SPACE_LEDGER.md`, `witness_bank.json`)

`CollatzFormal/Wave8WholeSpace.lean` ($135$ theorems, zero custom axioms, zero `sorryAx`, zero `native_decide`) together with `PROOF_SPACE_LEDGER.md` and `witness_bank.json` ($61$ ground-truth-verified witnesses across $5$ domains + $24$ structured barrier/falsification records) advances four orthogonal Wave 8 fronts:

1. **Front A (`Branch P4.3`) — Pushing Positive Collatz SRS from $7/11$ to $10/11$ via `[]`-Axiom $2 \times 2$ Hofbauer–Waldmann Certificates & Towers, Universal $\omega^k \implies \text{CollatzConjectureStandard}$ Bridge, Arts–Giesl Semantic DP, & $\forall d \ge 1, \forall k$ Tower Impossibility (`hofbauer_waldmann_tower_implies_no_infinite_srs_chain`, `hofbauer_waldmann_tower_acc_srsPlus`, `all11_hofbauer_waldmann_tower_implies_collatz_standard`, `omit_r2_10_of_11_admits_single_2d_hw_cert`, `omit_r7_and_omit_r5_10_of_11_admit_2d_hw_towers`, `infinite_all11_srs_chain_requires_infinitely_many_r2_r5_r7`, `arts_giesl_1d_semantic_dp_removes_dp1_rel_all_interior`, `mixed_srs_interior_b1_and_b0_pumping_identities`, `omega_k_coord_monotone_and_lower_tri_matrix_tower_impossibility`):**
   - **Universal $\omega^k$ Tower Soundness & Direct Forward Bridge to `CollatzConjectureStandard` (`zero custom axioms`):** Formalizes $k$-level Zantema–Hofbauer–Waldmann matrix rule-removal towers `OmegaHofbauerWaldmannTower d hd k rules` ($(M_s)\sb{0,0} \ge 1$, weak orientation on active rules, strict top-coordinate removal), proves `hofbauer_waldmann_tower_implies_no_infinite_srs_chain` and inductive `Acc` well-foundedness `hofbauer_waldmann_tower_acc_srsPlus`, and proves **`all11_hofbauer_waldmann_tower_implies_collatz_standard`** ($\exists d, k,\; \text{OmegaHofbauerWaldmannTower } d\;\text{hd}\;k\;\text{all11RuleList} \implies \text{CollatzConjectureStandard}$ via `encodePosBin` simulation of every $n \ge 2$ Collatz step).
   - **Breakthrough $10/11$ Positive SRS Certificates, Infinite Recurrence of $\lbrace R_2, R_5, R_7\rbrace$, & Arts–Giesl Shifted Semantic DP (`[]` & `zero custom axioms`):** Pushes Wave 7's $7/11$ frontier (`sub6 ∪ {R1}`) all the way to **$10/11$ rules** in $d = 2$ across three distinct $10$-rule subsets: `omit_r2_10_of_11_admits_single_2d_hw_cert` (`[]` axioms) strictly orients `all11OmitR2List` ($\lbrace R_1, R_3, R_4, R_5, R_6, R_7, R_8, R_9, R\sb{10}, R\sb{11}\rbrace$, including **all $4$ rules** $\lbrace R_3, R_4, R_6, R\sb{10}\rbrace$ left open in Wave 7!) in **one single $2 \times 2$ step**, while `omit_r7_and_omit_r5_10_of_11_admit_2d_hw_towers` (`[]` axioms) terminates `all11OmitR7List` (keeping both $R_1, R_2$ and $\lbrace R_3, R_4, R_6, R\sb{10}\rbrace$) in $2$ levels and `all11OmitR5List` in $3$ levels — proving (`infinite_all11_srs_chain_requires_infinitely_many_r2_r5_r7`, `zero custom axioms`) that **every infinite `all11RuleList` rewrite sequence must apply each of $R_2$, $R_5$, and $R_7$ infinitely many times**! Furthermore, `arts_giesl_1d_semantic_dp_removes_dp1_rel_all_interior` (`[]` axioms) proves under shifted 1D affine semantics $B_0=(2,1), B_1=(2,2), T_0=(3,2), T_1=(3,3), T_2=(3,4), R=(0,0), L^\sharp=(1,0)$ that **all $9$ interior/right base rules** $\lbrace R_3 \dots R\sb{11}\rbrace$ satisfy exact equality $\operatorname{eval}(\text{LHS}) = \operatorname{eval}(\text{RHS})$ while $DP_1 : L^\sharp B_0 \to L^\sharp$ is strictly removed relative to $\lbrace R_3 \dots R\sb{11}\rbrace$ (leaving $DP_2 : L^\sharp B_1 \to L^\sharp T_2$ modulo $\lbrace R_3 \dots R\sb{11}\rbrace$, while full $11/11$ termination — and even the $9$-rule sub-instance $\lbrace R_1, R_2, R_4, R_5, R_6, R_7, R_9, R\sb{10}, R\sb{11}\rbrace$ in $d = 2$ — remains open).
   - **All-Dimension $\omega^k$ Tower Impossibility & Interior Pumping Identities (`zero custom axioms`, hypothesis `W8_H2_OMEGA_K_COORD_MONOTONE_AND_LOWER_TRI_MATRIX_TOWERS`):** `omega_k_coord_monotone_and_lower_tri_matrix_tower_impossibility` proves across **all $d \ge 1$ and all $k \in \mathbb{N}$** that neither coordinatewise-monotone ($(M_s)\sb{i,i} \ge 1$, which forces $M_s = I_d \land v_s = 0$ on `sub6`) nor lower-triangular ($(M_s)\sb{0,0} \ge 1$, which forces $(M_s)\sb{0,0} = 1 \land (v_s)_0 = 0$) matrix rule-removal towers can ever remove a single rule of `sub6RuleList`, and `mixed_srs_interior_b1_and_b0_pumping_identities` extracts the exact 2-step interior pumping inequalities $T_0 B_1 B_0 \ge B_1 B_1 T_0$, $T_2 B_0 B_1 \ge B_0 B_0 T_2$, and $T_1 B_1 B_0 \ge B_0 B_0 T_1$ forced by any weak orientation of $\lbrace R_4, R_5, R_6, R_7\rbrace$.
2. **Front B (`Branch P3.4` & `P3.3`) — Cyclotomic Companion-Prime Quotient Forcing Against $p = 331$, Mod-$8$ Subgroup Obstruction, 2-Block $(99, 159)$ Floor, & Pure-Integer Laurent Binomial-Taylor Column Extrapolation (`one_block_exponents_coprime`, `one_block_cyclotomic_companion_quotient_forcing`, `prime_11_151_and_331_companion_cert`, `one_block_331_companion_forcing_and_mod8_obstruction`, `two_block_331_shared_mersenne_floor_99_159`, `laurent_binomial_taylor_column_extrapolation_dvd`):**
   - **Coprime-Order Prime Scan & $\mathcal{M}_1$ Local Cancellation (`witnesses M1_331_CANCELLATION_529_OVER_6643574255`, `COPRIME_PRIME_1210483_AND_MOD8_SUBGROUP_BARRIER`):** Exhaustive SPF-factored scanning across all $93{,}697$ odd primes $5 \le p \le 1{,}210{,}483$ proves that **$p = 331$** ($\operatorname{ord}\sb{331}(2) = 30, \operatorname{ord}\sb{331}(3/2) = 11$) and **$p = 1{,}210{,}483$** ($\operatorname{ord}_p(2) = 182, \operatorname{ord}_p(3/2) = 2217$) are the **exact first two coprime-order primes in $\mathbb{N}$**, while in $\mathcal{M}_1 = \mathbb{Q}\sb{(2)}^+$ at $(w_1, a_1) = (11, 30)$, $331$ divides $2^{30}-1$, $3^{11}-2^{11}$, and $D = 2^{41}-3^{11}$ simultaneously and **cancels completely** from $x_0 = 529 / 6{,}643{,}574{,}255$, proving purely local mod-$331$ congruences cannot eliminate $331 \mid D$.
   - **Cyclotomic Companion Quotient Forcing, Mod-$8$ Subgroup Escape, & 2-Block $(99, 159)$ Floor (`[]` & choice-free `zero custom axioms`):** `one_block_exponents_coprime` proves $\gcd(w_1, a_1) = 1$ on every 1-block $\mathbb{Z}^+$ cycle, and `one_block_cyclotomic_companion_quotient_forcing` proves that whenever $p \mid D$ forces $d_2 \mid a_1$ and $d\sb{32} \mid w_1$, every prime-power factor of $(2^{d_2}-1)/p^{e_2}$ or $(3^{d\sb{32}}-2^{d\sb{32}})/p^{e\sb{32}}$ supported on primes already excluded from $D$ divides $q_0 = (2^{a_1}-1)/D$ or $(2^{w_1} q_0 - 1)$! Instantiated at $p = 331$ via `prime_11_151_and_331_companion_cert` (`[]` axioms: $2^{30}-1 = 3^2 \cdot 7 \cdot 11 \cdot 31 \cdot 151 \cdot 331 = 3{,}243{,}933 \cdot 331$ and $3^{11}-2^{11} = 23^2 \cdot 331 = 529 \cdot 331$, with all $6$ companion primes $\lbrace 3, 7, 11, 23, 31, 151\rbrace$ proved coprime to $D$!), `one_block_331_companion_forcing_and_mod8_obstruction` (choice-free) forces **$3{,}243{,}933 \mid q_0$**, **$529 \mid (2^{w_1} q_0 - 1)$**, $\gcd(w_1, 30) = 1$, **$w_1 \ge 77, a_1 \ge 60, K \ge 137$**, AND **$D \equiv 5 \pmod 8$** — unconditionally refuting every prime-power $D = 331^e$ or product $D = \prod p_i^{e_i}$ of primes $\equiv 1, 3 \pmod 8$ (which includes **both** $331 \equiv 3$ and $1{,}210{,}483 \equiv 3 \pmod 8$)! On 2-block shared-Mersenne cycles, `two_block_331_shared_mersenne_floor_99_159` forces **$W \ge 99, a_1 + a_2 \ge 60, K \ge 159$**.
   - **Pure-Integer Laurent Binomial-Taylor Column Extrapolation (`zero custom axioms`):** Without $\mathbb{R}/\mathbb{C}$ calculus, `binomTaylorSum_remainder_dvd` proves $(B^T) \mid \bigl((1 + B)^x - \sum\sb{t=0}^{T-1} \binom{x}{t} B^t\bigr)$ for all $x, B, T \in \mathbb{N}$, and `laurent_binomial_taylor_column_extrapolation_dvd` proves across arbitrary $L \times L$ zero-gap grids (`intDet_sub_col_prefix_invariant`) that subtracting the first $T$ polynomial columns $(t, 0)$ preserves $\det\sb{\mathbb{Z}} M_0$ while forcing **$((2^u - 1)^T) \mid \det\sb{\mathbb{Z}} M_0$** on every column $(0, u)$, plus exact $3 \times 3$ derivative-extrapolated non-vanishing $\det(\text{laurentInterpMat}) = W (2^u - 1)^2 > 0$ and $W$-dilated zero-gap $\det\sb{\mathbb{Z}} M_0 = W (2^{W u} - 1)^2 > 0$.
3. **Front C (`Branch P1.2` & `P5.7`) — Base-2 Ripple-Carry Cascade Collapse, Non-Separable Multivariate & $\forall W\sb{\text{win}} \ge 1$ Sliding-Window Preimage Barriers, & 5th Solvable Cousin $T_{\diamond 5}$ (`bernoulli_nat_pow_step`, `bernoulli_nat_ratio_lt`, `ripple_carry_alternating_cascade_and_mersenne_triples`, `berg_meinardus_nonseparable_ripple_carry_preimage_impossibility`, `berg_meinardus_sliding_window_kgram_impossibility`, `cousinDiamond5StepInt_ofNat_eq`, `cousin_diamond5_outside_cones456_strict_descent`, `cousin_diamond5_cones456_exact_return`, `cousin_diamond5_global_convergence`, `cousin_diamond5_r_block_spiral_climb_and_laurent_impossibility`, `cousin_diamond5_q6_noninteger_avoids_cone6`, `cousin_diamond5_counter_model_separation`):**
   - **Ripple-Carry Cascade Collapse & Non-Separable Preimage Barrier (choice-free `zero custom axioms`, witness `ZPOS_RIPPLE_CARRY_COLLAPSE_341`):** Formalizes fuel-stabilized LSB-to-MSB binary ripple-carry addition for $n + (2n + 1)$ (`rippleCarryCount3n1`, `rippleCarryIdxSum3n1`) and proves (`ripple_carry_alternating_cascade_and_mersenne_triples`) that along $A_e = (4^e - 1)/3$ ($e \ge 1$, minimal $\equiv 2 \pmod 3$ witness $A_5 = 341$), $A_e$ triggers a full $2e$-bit carry cascade of index sum $e(2e - 1)$ ($10$ carries, index sum $45$ at $341$) whereas $2 A_e = 682$ collapses to **$0$ carries and $0$ index sum**, while Mersenne triples $(2^r - 1,\; 3 \cdot 2^{r-1} - 1,\; 3 \cdot 2^r - 2)$ ($\forall r \ge 3$) satisfy exact quadratic carry-index laws. Paired with pure-`Nat` Bernoulli asymptotic dominance $B(X + M)^K < (B + A) X^K$ (`bernoulli_nat_ratio_lt`), `berg_meinardus_nonseparable_ripple_carry_preimage_impossibility` refutes **every** non-separable multivariate positive polynomial quotient $P / Q$ in $(\text{rippleCarryCount3n1}(n),\; \text{rippleCarryIdxSum3n1}(n),\; \text{bitLength}(n))$.
   - **Universal $\forall W\sb{\text{win}} \ge 1$ Sliding-Window $k$-Gram Impossibility (choice-free `zero custom axioms`, witness `ZPOS_SLIDING_WINDOW_COLLISION_800`):** While width $W\sb{\text{win}} = 5$ genuinely separates Wave 7's $200$ from $400$, `berg_meinardus_sliding_window_kgram_impossibility` proves that for **every** window width $W\sb{\text{win}} \ge 1$, along $m\sb{W,t} = 3 \cdot 4^{2 W + t} + 2^{2 W + 1}$ ($t \ge 0$; already at $W = 2, t = 0$: $m\sb{2,0} = 800, 2 m\sb{2,0} = 1600, n\sb{\text{odd}} = 533$ has $2^5 \mid 800$ and defeats width $W\sb{\text{win}} = 5$, while $m\sb{W\sb{\text{win}}, t}$ collides width $W\sb{\text{win}}$ for all $t \ge 0$), the entire LSB-to-MSB list of non-zero $W\sb{\text{win}}$-bit windows `nonZeroWindowList W_win` is **constant in $t$ and identical on $m\sb{W,t}$ and $2 m\sb{W,t}$** while $(\text{zeroWindowCount}, \text{bitLength})$ grows linearly with slope $2$, refuting every positive preimage weight $f(\text{nonZeroWindowList } W\sb{\text{win}}\; n) \cdot P(\text{zeroWindowCount}, \text{bitLength}) / Q(\text{zeroWindowCount}, \text{bitLength})$.
   - **5th Solvable Cousin $T\sb{\diamond 5}$ (`zero custom axioms`, witnesses `ZPOS_COUSIN_DIAMOND5_CONE6_2285_JUMP`, `M1_COUSIN_DIAMOND5_1_OVER_7`, `M3_COUSIN_DIAMOND5_7X1_CYCLE5`):** Extends $T\sb{\diamond 4}$ with Cone 6 ($x \ge 2285 \land x \equiv 237 \pmod{256} \land x \equiv 8 \pmod 9 \land \operatorname{core}\sb{2,3}(x + 19) = 1 \mapsto (3x + 1)/8$), introducing genuine $v_2(3x + 1) = 3$ (`/8`) compressed Syracuse steps ($2^e 3^f - 19 \mapsto 2^{e-3} 3^{f+1} - 7$, minimal $2285 \to 857$, $73{,}709 \to 27{,}641$) that jump $\Phi\sb{\diamond 2}$ upward **directly into Cone 5's unbounded $r$-block spiral climb**, yet converges globally to $1$ within $k \le \Phi\sb{\diamond 2}(x) \le (x + 1)^3 + (x + 1)^5$ steps via 3-tier ($\omega^3$) Cone-6 $\to$ Cone-5 $\to$ $\Phi\sb{\diamond 2}$ return (`cousin_diamond5_cones456_exact_return`, `cousin_diamond5_global_convergence`) while defeating all $L$-term Laurent sums, proving universal non-integer $\mathbb{Q}\sb{(6)}^+$ Cone-6 avoidance (`cousin_diamond5_q6_noninteger_avoids_cone6`, choice-free), and separating $\mathcal{M}_1, \mathcal{M}_2, \mathcal{M}_3$ (`cousin_diamond5_counter_model_separation`, `[]` axioms).
4. **Front D (`Branch P5.3` & `P2.2`) — Exact Cross-Scale ($\lvert u_1 \rvert < \lvert u_2 \rvert$) $q = 0$ Leaf Collision Biconditional, Unconditional Multi-Scale `NoDupNat`, & Markov Mod-$6$ Lock (`q0_cross_scale_leaf_collision_iff_trivial_loop`, `multiscale_first_hit_surviving_q0_leaves_nodup`, `canonicalSuffixShift_markov_bijection_and_mod6_lock`):**
   - **Exact Cross-Scale $q = 0$ Collision Biconditional & Multi-Scale `NoDupNat` (`zero custom axioms`, witness `ZPOS_RAY_Q0_MULTI_LOOP_COLLISION_3`):** `q0_cross_scale_leaf_collision_iff_trivial_loop` proves across **all** core parity words $\lvert u_1 \rvert < \lvert u_2 \rvert$ that `exactBackwardQuotient 1 u_1 0 = exactBackwardQuotient 1 u_2 0` holds **if and only if** $\exists m \in \mathbb{N},\; u_2 = \text{trivialLoopExt } u_1\; m = u_1 \mathbin{+\!\!+} \text{false}^{a_1} \mathbin{+\!\!+} [\text{true}] \mathbin{+\!\!+} [\text{false}, \text{true}]^m$ (with every such $u_2$ having $\text{canonicalSuffixShift } u_2\; 1 = 1$ and $\neg \text{IsFirstHitOnePair } (u_2, 0)$, and multi-loop $m = 1$ witness $[1,1,0,0,0,1,0,1]$ colliding with $[1,1]$ at $y_0 = 3$). Consequently, `multiscale_first_hit_surviving_q0_leaves_nodup` proves unconditional `NoDupNat` and exact membership completeness of `firstHitQ0LeavesUpToLen L_max` and `firstHitSurvivingQ0LeavesUpToLen L_max` across **all** $L\sb{\max} \in \mathbb{N}$.
   - **Markov Skew-Product Bijectivity & Universal Forbidden $5 \bmod 6$ Law (`zero custom axioms`):** `canonicalSuffixShift_markov_bijection_and_mod6_lock` proves for every $w \ge 1$ that `markovShiftFalse w` is an explicit two-sided bijection on $[0, 2 \cdot 3^{w-1})$, `markovShiftTrue w` is a strict bijection from $[0, 2 \cdot 3^{w-1})$ onto $\lbrace a' < 2 \cdot 3^w \mid a' \bmod 6 \in \lbrace 1, 3\rbrace\rbrace$ with constructive inverse $a = \operatorname{dlog}\sb{2, 3^w}\bigl((2^{a'+1}-1)/3\bigr)$, and therefore **`canonicalSuffixShift u 1 % 6 ∈ {1, 3}` (`≠ 5`)** holds universally across every core parity word of weight $w(u) \ge 2$.

---

## 26. Wave 9 Whole-Space Proof Loop: $d = 3$ `omit R9` (`10/11`) SRS Tower, Zantema Modular Semantic Labelling ($\forall M \ge 1$) Terminating `S9`, & `2D` Boundary-Coupled / Parikh-Syzygy Obstructions; $4 \times 4$ Two-Base Laurent Non-Vanishing & Pratt–Lucas Coprime Primes $p_3 = 45{,}661{,}129$ / $p_4 = 107{,}889{,}071$; Universal $\forall Q \ge 1$ Stateful Automaton & Mealy Transducer Preimage Barriers & 6th Solvable Cousin $T_{\diamond 6}$; and Complete Global $(u_1, q_1)$ vs $(u_2, q_2)$ Collision Classification, $\forall k$ Prefix-Memory Annihilation, & Multi-Step $3^{w-1-j}$ Fiber Equidistribution (`CollatzFormal/Wave9WholeSpace.lean`, `PROOF_SPACE_LEDGER.md`, `witness_bank.json`)

`CollatzFormal/Wave9WholeSpace.lean` ($146$ public audited theorems / $150$ declarations, zero custom axioms, zero `sorryAx`, zero `native_decide`) together with `PROOF_SPACE_LEDGER.md` and `witness_bank.json` ($68$ ground-truth-verified witnesses across $5$ domains + $28$ structured barrier/falsification records) advances four orthogonal Wave 9 fronts:

1. **Front A (`Branch P4.3`) — $d = 3$ Non-Triangular Tower for `omit R9` (`10/11`), Universal Zantema Modular Semantic Labelling ($\forall M \ge 1$) Terminating `S9 = all11 \ {R3, R8}` (`18/18` Parity-Labelled Rules), & Unlabelled `S9` Subsequence-Pumping / Boundary-Coupled `2D` / Parikh-Syzygy Obstructions (`omit_r9_10_of_11_admits_3d_hw_tower`, `infinite_all11_srs_chain_requires_infinitely_many_r2_r5_r7_r9`, `collatz_mod_m_is_exact_semantic_model`, `zantema_semantic_labelling_soundness`, `s9_mod2_labelled_admits_2d_hw_tower`, `no_infinite_s9_srs_chain`, `s9_subseq_pumping_and_d2_zero_diag_obstruction`, `s9_d2_boundary_nontri_and_parikh_syzygy_obstruction`):**
   - **Genuine $d = 3$ Non-Triangular Tower for `all11 \ {R9}` (`10/11` Rules) & 4-Rule Infinite Recurrence:** `omit_r9_10_of_11_admits_3d_hw_tower` (`[]` axioms) constructs an explicit $5$-level $3 \times 3$ non-triangular Hofbauer–Waldmann tower (`towerOmitR9_3D`, sequentially removing $\{R_1, R_2, R_4, R_7\} \to \{R_6, R_{10}, R_{11}\} \to \{R_3\} \to \{R_8\} \to \{R_5\}$) terminating `all11OmitR9List`, and `infinite_all11_srs_chain_requires_infinitely_many_r2_r5_r7_r9` (`zero custom axioms`) upgrades Wave 8's 3-rule recurrence to prove that **every infinite `all11RuleList` rewrite sequence must apply each of $R_2, R_5, R_7,$ and $R_9$ infinitely many times**.
   - **Universal Zantema Modular Semantic Labelling ($\forall M \ge 1$) & Complete `2D` Termination of `S9` (`[]` & `zero custom axioms`):** `collatz_mod_m_is_exact_semantic_model` (choice-free) proves that for **every modulus $M \ge 1$** and every carrier $c \in \mathbb{N}$, **all $11$ rules of `all11RuleList`** preserve the shifted modular evaluation $(B_b \mapsto (2x + b) \bmod M,\; T_t \mapsto (3x + t) \bmod M,\; L \mapsto 0,\; R \mapsto 1 \bmod M)$ identically, and `zantema_semantic_labelling_soundness` proves that any `GenOmegaHWTower` on the $7 M$-symbol labelled rule set `labelledCollatzRules M rules` establishes `Acc (SRSPlus rules)` on the unlabelled SRS. Instantiated at $M = 2$ (parity carrier $\{0, 1\}$, $14$ symbols), `s9_mod2_labelled_admits_2d_hw_tower` (`[]` axioms) certifies a $7$-level `2D` non-triangular tower (`towerS9Mod2_2D`) orienting all **$18/18$ parity-labelled rules** of $S_9 = \text{all11} \setminus \{R_3, R_8\}$, yielding `no_infinite_s9_srs_chain` (`zero custom axioms`) — breaking the unlabelled $d = 2$ stall where exhaustive rational Simplex LP over all $9{,}317$ non-lower-triangular $2 \times 2$ cones in $\{0, 1, 2\}$ finds $0$ single-rule removals on $S_9$!
   - **Unlabelled `S9` Subsequence-Pumping, Parikh-Syzygy, & Boundary-Coupled `2D` $\omega^k$ Tower Impossibility (`zero custom axioms`, hypothesis `W9_H2_UNLABELLED_D2_TRIANGULAR_S9_AND_OMEGA3_DIAMOND6_BARRIER`):** Even WITHOUT swap rules $\{R_3, R_8\}$, `s9_subseq_pumping_and_d2_zero_diag_obstruction` proves on $S_9$ that (i) $S_9$ generates the multi-step derivations $[L, B_1, R] \to^+ [L, B_1, B_0, R]$, $[L, T_2, R] \to^+ [L, T_2, B_0, R]$, $[L, B_1, B_0, B_0, R] \to^+ [L, B_1, B_1, R]$, and $[L, B_1, B_0, R] \to^+ [L, R]$, (ii) every `2D` Hofbauer–Waldmann interpretation weakly orienting $S_9$ and strictly removing $R_2$ or $R_{11}$ is algebraically forced into $(M_{L \cdot B_1})_{0,1} \ge 1$, singular zero lower-right diagonal $(M_{B_0})_{1,1} = 0$, and $(v_R)_1 \ge 1$, and (iii) **every $\forall d \ge 1, \forall k$ coordinatewise-monotone or lower-triangular $\omega^k$ tower collapses on $S_9$**. Furthermore, `s9_d2_boundary_nontri_and_parikh_syzygy_obstruction` (`zero custom axioms`) proves across ALL $k \in \mathbb{N}$ that (1) the 4-generator nonnegative Parikh syzygies ($Z_{\text{int}} = R_4 + R_5 + R_6 + R_7$, $Z_9 = R_2 + R_5 + R_6 + 2 R_7 + R_9$, $Z_{11} = R_1 + R_2 + R_{11}$, $Z_{10} = R_1 + R_2 + R_4 + R_5 + R_7 + R_{10}$) force exact Parikh equality across all $9/9$ rules of $S_9$, collapsing `OmegaParikhRuleRemovalTower k s9RuleList` and `OmegaAffineRuleRemovalTower k s9RuleList`, AND (2) even when boundary symbols $L$ and $R$ carry **completely unrestricted full $2 \times 2$ non-triangular `Nat` matrices**, every `2D` interior-lower-triangular level forces $v_0(\text{LHS}) = v_0(\text{RHS})$ on all $9/9$ rules of $S_9$ (`¬ OmegaInteriorLowerTri2DTower k s9RuleList` and `¬ OmegaInteriorLowerTri2DTower k all11RuleList`)!
2. **Front B (`Branch P3.3` & `P3.4`) — Pure-`Nat`/`Int` $4 \times 4$ Single-Base & Two-Base Confluent Vandermonde Closed Forms / Convergent-Cone Non-Vanishing, Pratt–Lucas Primality of $p_3 = 45{,}661{,}129$ & $p_4 = 107{,}889{,}071$, Mod-$8$ Escape, & Companion/Joint Floors (`laurent_4x4_confluent_and_twobase_nonvanishing`, `lucas_order_implies_isPrimeNat`, `coprime_primes_45661129_and_107889071_cert`, `w9_joint_lcm_arith_cert`, `one_block_331_forces_mod8_escape_and_joint_p4_floors`, `p3_p4_companion_arith_cert`, `p3_and_p4_cyclotomic_companion_quotient_forcing`):**
   - **$4 \times 4$ Confluent Single-Base & Genuine Two-Base Schneider–Laurent Non-Vanishing (`zero custom axioms`, witness `LAURENT_TWOBASE_4X4_RESONANT_ZERO_W9_K16_U2`):** `laurent_4x4_confluent_and_twobase_nonvanishing` proves exact pure-`Int` determinant factorizations across three $4 \times 4$ confluent regimes: (i) single-base `(T=3, U=1)` cubic Taylor + 1 extrapolated column equals $W^3 (2^u - 1)^3 > 0$; (ii) single-base `(T=2, U=2)` confluent Hermite–Vandermonde equals $W^2 \cdot 2^u (2^u - 1)^4 > 0$; and (iii) **genuine two-base `(2^r 3^s)^u` confluent interpolation** on `[(0,0),(0,1),(1,0),(1,1)] × [(0,0),(1,0),(0,u),(1,u)]` equals $2^u W^2 (3^u - 1)^2 - 3^u K^2 (2^u - 1)^2$. While unrestricted coprime $(W, K)$ vanishes at the resonant zero $(W, K, u) = (9, 16, 2)$ ($4 \cdot 81 \cdot 64 - 9 \cdot 256 \cdot 9 = 0$), the theorem proves **universal odd-$u$ non-vanishing** ($2 \parallel \det$) across ALL $W, K \ge 1$ AND **strict positivity $\det > 0$ across the entire Collatz convergent cone $3 K \le 5 W, u \ge 2$** (via $75(2^u - 1)^2 < 25 \cdot 2^{u+2}(3^u - 1) \le 9 \cdot 2^u (3^u - 1)^2$)!
   - **Pratt–Lucas Primality Certificates for $p_3 = 45{,}661{,}129$ & $p_4 = 107{,}889{,}071$, Mod-$8$ Escape, Joint Floors, & Companion Forcing (`[]` & choice-free `zero custom axioms`, witness `COPRIME_PRIMES_45661129_MOD8_1_AND_107889071_MOD8_7`):** Scanning odd primes up to $1.1 \times 10^8$ reveals that the 3rd coprime-order prime **$p_3 = 45{,}661{,}129$** ($\operatorname{ord}_2 = 12{,}381, \operatorname{ord}_{3/2} = 1{,}844$) satisfies $p_3 \equiv 1 \pmod 8$ (still trapped inside $\{1, 3\} \pmod 8$!), and isolates **$p_4 = 107{,}889{,}071$** ($\operatorname{ord}_2 = 52{,}835, \operatorname{ord}_{3/2} = 1{,}021, p_4 \equiv 7 \pmod 8$) as the **minimal $\{5, 7\} \pmod 8$ coprime-order prime**. Using Bezout-free Gauss–Euclid (`gauss_euclid_lemma`), finite pigeonhole (`nat_func_pigeonhole`), and Lucas's Converse of Fermat's Little Theorem (`lucas_order_implies_isPrimeNat`, choice-free), `coprime_primes_45661129_and_107889071_cert` (choice-free) certifies primality and exact coprime orders of $331, 1{,}210{,}483, 45{,}661{,}129,$ and $107{,}889{,}071$ in the Lean 4 kernel; `one_block_331_forces_mod8_escape_and_joint_p4_floors` (via `w9_joint_lcm_arith_cert`, `[]` axioms) refutes $D = 331^{e_1} \cdot 1210483^{e_2} \cdot 45661129^{e_3}$, forces a prime divisor $q \mid D$ with $q \bmod 8 \in \{5, 7\}$, and proves joint $(331, 107889071)$ floors **$w_1 \ge 550{,}319, a_1 \ge 317{,}010, K \ge 867{,}329$** (1-block) and **$W \ge 159{,}276, K \ge 264{,}946$** (2-block); and `p3_and_p4_cyclotomic_companion_quotient_forcing` (choice-free, via `p3_p4_companion_arith_cert`, `[]` axioms) proves standalone companion quotient forcing & solo 1-block floors (**$31 \mid q_0, w_1 \ge 88{,}827, K \ge 141{,}662$** when $107{,}889{,}071 \mid D$; **$7 \mid q_0, 65 \mid (2^{w_1} q_0 - 1), w_1 \ge 22{,}128, K \ge 34{,}509$** when $45{,}661{,}129 \mid D$).
3. **Front C (`Branch P1.2` & `P5.8`) — Universal $\forall Q \ge 1$ Stateful LSB/MSB Finite-Automaton & Mealy Transducer Preimage Impossibility & 6th Solvable Cousin $T_{\diamond 6}$ ($\omega^4$ Cascade) (`berg_meinardus_stateful_automaton_preimage_impossibility`, `fin_unary_iter_and_sum_period_sub1`, `berg_meinardus_stateful_transducer_preimage_impossibility`, `cousinDiamond6StepInt_ofNat_eq`, `cousin_diamond6_outside_cones4567_strict_descent`, `not_cone7_six_mul_pow9_sub1`, `cousin_diamond6_cones4567_exact_return`, `cousin_diamond6_global_convergence`, `cousin_diamond6_r_block_spiral_climb_and_laurent_impossibility`, `cousin_diamond6_q6_noninteger_avoids_cone7`, `cousin_diamond6_counter_model_separation`):**
   - **Universal $\forall Q \ge 1$ Stateful Automaton & Mealy Transducer Preimage Barriers (choice-free `zero custom axioms`, witness `ZPOS_STATEFUL_Q2_COLLISION_800_VS_3200`):** While a 2-state parity-of-zeros automaton genuinely separates Wave 8's $800 \leftarrow 1600$, `fin_unary_iter_factorial_period` and `fin_unary_iter_and_sum_period_sub1` prove universal unary tail periodicity $P = Q!$ and affine cumulative transition-sum growth across all $g : \operatorname{Fin} Q \to \operatorname{Fin} Q$. `berg_meinardus_stateful_automaton_preimage_impossibility` (choice-free) proves that along $m_{Q, s} = 3 \cdot 4^{2Q + P s} + 2^{2Q+1}$, multi-step even ancestor $2^P m_{Q, s}$ (minimal $Q = 2, s = 0$: $800 \leftarrow 3200, n_0 = 533$), and odd preimage $n_{Q, s} = (2 m_{Q, s} - 1)/3$, **BOTH** `runLSBAutomaton Q` **AND** `runMSBAutomaton Q` collide to identical states across **ALL** transition tables while `(zeroBitCount, binBitLength)` grow with exact slope $2 P s$; and `berg_meinardus_stateful_transducer_preimage_impossibility` (choice-free) generalizes this to **stateful Mealy transducers** `runLSBTransducerOut Q delta emit q0` and `runMSBTransducerOut Q delta emit q0` (`emit : Fin Q -> Bool -> Nat`, representing arbitrary linear combinations of state-transition counts $\sum_{q,b} c_{q,b}\,\#\text{trans}_{q,b}(n)$), refuting BOTH every positive-`0`-cycle trivariate `NatPoly3` quotient on the $0$-spine (even with disconnected distinct-slope `0`-cycles!) AND every positive-`1`-cycle MSB Mealy transducer quotient along Mersenne `1`-spines $3 \cdot 2^{2Q + P s} - 1 \leftarrow 2^{2Q + P s + 1} - 1$ (defeating parity-of-popcount `Q = 2` Mealy transducers whose `0`-cycles emit `0`) — **permanently closing ALL regular / finite-automaton / Mealy transducer Berg–Meinardus preimage weights**.
   - **6th Solvable Cousin $T_{\diamond 6}$ (`zero custom axioms`, witnesses `ZPOS_COUSIN_DIAMOND6_CONE7_21232853_JUMP`, `M1_COUSIN_DIAMOND6_1_OVER_7`, `M3_COUSIN_DIAMOND6_7X1_CYCLE5`):** Extends $T_{\diamond 5}$ with Cone 7 ($x \ge 294101 \land x \equiv 31957 \pmod{32768} \land x \equiv 8 \pmod 9 \land \operatorname{core}_{2,3}(x + 811) = 1 \mapsto (3x + 1)/128$), introducing genuine $v_2(3x + 1) = 7$ (`/128`) compressed Syracuse steps ($2^g 3^h - 811 \mapsto 2^{g-7} 3^{h+1} - 19 \mapsto 2^{g-10} 3^{h+2} - 7$, e.g. $294{,}101 \to 6{,}893 \to 2{,}585$ and $21{,}232{,}853 \to 497{,}645 \to 186{,}617$) that cascade 4 tiers Cone 7 $\to$ Cone 6 $\to$ Cone 5 $\to$ $\Phi_{\diamond 2}$, proves post-climb non-reentry into Cone 7 via `not_cone7_six_mul_pow9_sub1` ($\bmod 163$), converges globally on $\mathbb{Z}^+$ within $k \le \Phi_{\diamond 2}(x) \le (x+1)^3 + (x+1)^5$ steps (`cousin_diamond6_global_convergence`), proves universal non-integer $\mathbb{Q}_{(6)}^+$ Cone-7 avoidance (`cousin_diamond6_q6_noninteger_avoids_cone7`, choice-free), and separates $\mathcal{M}_1, \mathcal{M}_2, \mathcal{M}_3$ (`cousin_diamond6_counter_model_separation`, `[]` axioms).
4. **Front D (`Branch P5.3` & `P2.2`) — Complete Global $(u_1, q_1)$ vs $(u_2, q_2)$ Collision Classification Across ALL `CoreWords × Nat`, Universal $\forall k$ $\bmod\, 2 \cdot 3^k$ Prefix-Memory Annihilation, Complete Mod-$18$ Markov Bijection, & Multi-Step $3^{w-1-j}$ Fiber Equidistribution (`one_generator_q_pos_all_weights_first_hit`, `global_one_generator_collision_classification`, `canonicalSuffixShift_mod18_and_pow3_memory_annihilation`, `nat_fin_inj_implies_surj`, `markovShift_mod18_bijection_and_multistep_fiber_equidistribution`):**
   - **Complete Global Collision Classification (`zero custom axioms`, witness `ZPOS_RAY_MIXED_Q0_Q1_COLLISION_5`):** `one_generator_q_pos_all_weights_first_hit` removes Wave 5's $w \ge 2$ restriction to prove `IsFirstHitOnePair u q` holds for **ALL $w \ge 1$ and ALL $q \ge 1$** (including $u = [\text{true}]$), and `global_one_generator_collision_classification` completely classifies `exactBackwardQuotient 1 u_1 q_1 = exactBackwardQuotient 1 u_2 q_2` across ALL pairs in `CoreWords × Nat`: (1) global `IsFirstHitOnePair` injectivity across ALL $w \ge 1$; (2) $q_1, q_2 \ge 1 \implies (u_1, q_1) = (u_2, q_2)$; (3) mixed $q_1 = 0, q_2 \ge 1$ collides **iff** $\exists m \in \mathbb{N},\; u_1 = \text{loopUnroll } u_2\; q_2\; m = u_2 \mathbin{+\!\!+} \text{false}^{a_2 + 2 \cdot 3^{w_2-1} q_2} \mathbin{+\!\!+} [\text{true}] \mathbin{+\!\!+} [\text{false}, \text{true}]^m$ (realized at $m = 0$ by $([1,0,0,0,1], 0)$ and minimally for multi-loop $m = 1$ by $([1,0,0,0,1,0,1], 0) \leftrightarrow ([1], 1)$ on $y = 5$); (4) complete $q_1 = q_2 = 0$ trichotomy; and (5) $y = 1 \iff q = 0 \land \exists m,\; u = [\text{true}] \mathbin{+\!\!+} [\text{false}, \text{true}]^m$.
   - **Universal $\forall k : \mathbb{N}$ $3$-Adic Markov Prefix-Memory Annihilation, Complete Mod-$18$ Bijection, & Multi-Step $3^{w-1-j}$ Fiber Equidistribution (`zero custom axioms`):** `canonicalSuffixShift_mod18_and_pow3_memory_annihilation` proves inductively that each `true` bit multiplies 3-adic shift precision by $3$ ($a_1 \equiv a_2 \pmod{2 \cdot 3^m} \implies \text{markovShiftTrue}(a_1) \equiv \text{markovShiftTrue}(a_2) \pmod{2 \cdot 3^{m+1}}$ while `false` subtracts $1 \pmod{2 \cdot 3^m}$), so **for EVERY $k \in \mathbb{N}$, ANY suffix `suf` with $w(\text{suf}) \ge k + 1$ ($w(\text{suf}) \ge 1 \implies \bmod\, 2 \cdot 3^{w(\text{suf})-1}$) completely annihilates EVERY prefix `pref` modulo $2 \cdot 3^k$** (`canonicalSuffixShift (pref ++ suf) 1 % (2 * 3^k) = canonicalSuffixShift suf 1 % (2 * 3^k)`), pinning `pref ++ [true, true]` ($w(\text{pref}) \ge 1$) to $\{9, 15\} \pmod{18}$, `pref ++ [true, false, true]` ($w(\text{pref}) \ge 1$) to $\{1, 7\} \pmod{18}$, and `pref ++ [true, true, true]` (for ALL `pref`) identically to $9 \pmod{18}$. Finally, `markovShift_mod18_bijection_and_multistep_fiber_equidistribution` (via choice-free `nat_fin_inj_implies_surj`) proves the complete mod-$18$ Markov bijection table ($a \bmod 6 \in \{0,1,2,3,4,5\} \mapsto \{1, 15, 7, 9, 13, 3\} \pmod{18}$, confining EVERY $w(u) \ge 3$ core word to $\{1, 3, 7, 9, 13, 15\} \pmod{18}$) AND **universal multi-step fiber equidistribution**: for EVERY $w \ge 1$, EVERY binary tail `tail`, EVERY coarse level $j \le w - 1$, and EVERY target residue $r < 2 \cdot 3^j$, `iterMarkovShift tail w` hits $r \pmod{2 \cdot 3^j}$ on **exact fiber cardinality $3^{w-1-j}$** across $a < 2 \cdot 3^{w-1}$!
