# Collatz Conjecture: 2-Adic Dynamics, Unconditional $m$-Cycle Elimination ($m \le 99$), & Pure-Kernel Lean 4 Proofs

A formal-methods and computational number-theory research suite combining **Lean 4** pure-kernel theorem proving (zero external dependencies, zero `sorry`, zero `native_decide`, zero custom axioms), a **zero-dependency Python** analytical/verification library, and a **portable C23** native 2-adic Hensel search kernel (`_hensel_fast.c`).

For full derivations and theorem-by-theorem mathematical exposition, see [`collatz_analysis/MATHEMATICAL_FINDINGS.md`](collatz_analysis/MATHEMATICAL_FINDINGS.md).

---

## What Was Proved

All claims explicitly track their hypotheses: pure algebraic, 2-adic, Diophantine, and equivalence theorems are proved **unconditionally** inside Lean 4; cycle non-existence results above $N_0 = 2^{71}$ explicitly assume Laurent–Mignotte–Nesterenko linear forms in logarithms (`BakerLMNPowerBound`) and Barina's (2025) computational convergence verification threshold (`BarinaThreshold (2 ^ 71)`).

### 1. Unconditional Positive $m$-Cycle Elimination Through $1 \le m \le 99$
- **Pure Lean 4 Kernel Pipeline ($1 \le m \le 93$ + higher-weight $m = 94..96$ tails):** Assuming only `BarinaThreshold (2 ^ 71)` and `BakerLMNPowerBound`, `CollatzFormal/HenselBridge93To96.lean` proves `no_nontrivial_spiral_cycles_1_to_93` end-to-end inside the Lean 4 kernel with zero external trust gap, plus `u >= 2` at $m = 94$, `u >= 3` at $m = 95$, and `u >= 4` at $m = 96$.
- **C23 + Lean 4 Hybrid Frontier ($1 \le m \le 99$):** Extending beyond Steiner ($m = 1$) and Hercher ($m \le 91$), Theorem 33 (`prove_m99_unconditional_hensel_frontier` in `goal_extensions.py`) eliminates all positive spiral $m$-cycles for **$1 \le m \le 99$** at $N_0 = 2^{71}$, with **all newly discovered $m = 97..99$ arithmetic survivors ($19{,}175$ pairs in `CollatzFormal/Survivors97To99A`..`J.lean`, alongside $8{,}139$ pairs in `CollatzFormal/Survivors.lean`) independently verified to drop $\le 2^{71}$ in the Lean 4 kernel via `by decide`** (`m97_to_99_hensel_survivor_drop_universal`).

### 2. Canonical Conjecture Equivalences & Mod-$1296$ Sieved Syracuse Forest (`Core.lean`, `BoostMechanisms.lean`)
Proved inside the Lean 4 kernel (`↔` iff):
- Equivalence of `CollatzConjectureStandard` to the compressed Terras map, strict stopping-time descent, the two-barrier conjunction `NoDivergentPositiveOrbits ∧ NoNontrivialPositiveCycles`, and side-condition-free One-Equation Diophantine solvability (`collatz_iff_one_equation_diophantine`).
- Exact global injectivity of the in-degree-$0$ multi-root inverse Syracuse forest and kernel-verified equivalence `CollatzConjectureStandard ↔ Mod1296SievedForestCarryCollisionProp` (Theorem 32.3e).
- Concatenated carry law `affineCarry_append`, two-return Garden-of-Eden escape (`two_return_garden_of_eden_escape` forcing $x_2 \not\equiv 0 \pmod 3$ on every positive-weight return), $(\mathbb{Z}/81\mathbb{Z})^\times$ suffix-shift surjectivity (`two_return_escape_suffix_congruence_mod81`), and reduction of minimal-counterexample residue classes modulo $1296 = 2^4 \cdot 3^4$ to $131 / 1296 \approx 10.1080\%$ (Theorem 32).

### 3. Structural Number-Theory & Obstruction Results (Theorems 1–33)
- **2-Adic Homeomorphism & Beatty–Sturmian Carry Bounds:** Measure-preserving 2-adic parity bijection, exact Cramér large-deviation rate $1 - H_2(\log_3 2)$, ultrametric carry decoding, and Myhill–Nerode state complexity ($3^w$ reachable carry states).
- **Diophantine & $p$-Adic Cycle Classifications:** Catalan–Mihăilescu unit denominators ($|2^k - 3^w| = 1$), $N_0$-free $2$- and $3$-cycle classifications over $\mathbb{Z}$, $S$-integer cycles in $\mathbb{Z}[1/30]$, and complete classification of $|2^k - 3^w| = 5^e$.
- **Mandatory $3 \times 3$ Counter-Model Audit:** Candidate mechanisms are tested against three known obstructions—$\mathbb{Q}_{(2)}^+$ cycles ($19/5, 29/5$), $\mathbb{Z}^-$ cycles ($-1, -5, -17$), and $5n+1$ positive cycles ($5, 13, 17$)—to catch unsound generalizations early.

### 4. Lean 4.35.0 Kernel Audit Summary
- **Toolchain:** `leanprover/lean4:v4.35.0` (zero external Lake dependencies).
- **Files:** `50` `.lean` files (`CollatzFormal.lean` + `49` modules under `CollatzFormal/`).
- **Verified Theorems/Lemmas:** `957` declarations compiled cleanly with `--wfail`, zero warnings, zero `sorryAx`, zero `native_decide`, and zero custom axioms (`521` theorems completely axiom-free `[]`; all remaining theorems rely only on Lean's standard foundational axioms `Classical.choice`, `Quot.sound`, `propext`).

---

## How It Was Done

1. **Rational-Logarithm Slabs & $q_{43}$ Lattice Confinement:** Upper convergents/semiconvergents of $\log_2 3$ (specifically $p_{43}/q_{43}$ with $q_{43} = 205{,}632{,}218{,}873{,}398{,}596{,}256$) pin any hypothetical cycle's total odd/even counts $(W, K)$ to narrow congruence strips and give monotone $u$-tail cutoffs ($u_{\text{cut}} = 14, 15, 15$ at $m = 97, 98, 99$).
2. **Two-Vertex $(x_{(1)}, x_{(2)})$ Reciprocal-Budget Split & $4$-Shell De Morgan Climb:** For low multiplicity ($u = 1$) at $m \in \{97, 98, 99\}$, reciprocal-budget constraints $\sum 1/x_i$ are partitioned into dyadic $(x_{(1)}, x_{(2)})$ strips with $s_{\text{low}}$-stratified cutoffs and sorted-cycle dominance checks (showing `(99, 1)` bounds dominate `(97, 1)` and `(98, 1)`).
3. **2-Adic Hensel Tree Pruning in C23 (`_hensel_fast.c`):** A compiled C23 shared library (`clang -std=c23 -O3`) performs recursive multi-step Hensel tree enumeration with modular tables and cyclic pigeonhole pruning, separating empty congruence branches from genuine arithmetic survivors above $2^{71}$.
4. **Independent Kernel Certification (`by decide`):** Every surviving starting candidate $(n, \text{steps})$ emitted by the C23/GPU search is serialized into Pure-`Nat` Lean 4 tables (`CollatzFormal/Survivors*.lean`) and independently re-executed inside Lean 4's kernel via `checkSurvivorDrop` / `checkSurvivorBatchFast_sound`.

---

## Repository Structure

```text
collatz_analysis/
├── __init__.py                    # Public API exports
├── cli.py                         # Command-line summary & trajectory analyzer
├── parity_2adic.py                # 2-adic parity bijection, affine carries, Collatz/Syracuse steps
├── cycles.py                      # Continued fractions of log2(3), Steiner 1-cycle, Eliahou bounds
├── stopping_time.py               # Beatty-Sturmian bounds, DP stopping-time sieve, Cramér rate
├── coalescence_and_mcycles.py     # Ultrametric carry decoding, coalescence sieve, m-cycle identities
├── frontier_reductions.py         # One-equation equivalence, Raney cone, no-go meta-theorem
├── mcycles_and_cantor_cone.py     # Semiconvergent records, Cantor cone, m-cycle elimination
├── boost_obstructions.py          # Brox finiteness, p-adic Baker S-integer bounds, m=92 certificates
├── goal_extensions.py             # Potential-telescoping horizon & m <= 99 C23/Lean hybrid pipeline
├── boost_mechanisms.py            # Mod-1296 sieve, two-return escape, multi-root forest mixing
├── formal_proofs.py               # Automated Lean 4 compiler & `#print axioms` audit harness
├── _hensel_fast.c                 # Portable C23 multi-step 2-adic Hensel acceleration library
├── MATHEMATICAL_FINDINGS.md       # Detailed mathematical documentation (Theorems 1-33 + Lean 4)
├── lakefile.lean                  # Lean 4 Lake build configuration
├── lean-toolchain                 # Lean toolchain pin (leanprover/lean4:v4.35.0)
├── lake-manifest.json             # Lake manifest (zero external dependencies)
├── CollatzFormal.lean             # Root Lean 4 umbrella module
├── CollatzFormal/                 # 49 Lean 4 submodules (Core, RationalLogSlabs, Survivors*, HenselBridge*)
└── tests/
    └── test_collatz.py            # Unit test & Lean 4 / Theorem 1-33 verification suite
```

---

## Usage & Verification

### Prerequisites
- **Python 3.11+** (no third-party Python packages required)
- **C23 compiler** (`clang` on PATH or bundled in `~/.elan/toolchains/*/bin`) — auto-compiled on demand by `collatz_analysis` into `_hensel_fast.{dll,so,dylib}`, or compile manually:
  ```bash
  # Linux / macOS
  clang -std=c23 -O3 -shared -fPIC collatz_analysis/_hensel_fast.c -o collatz_analysis/_hensel_fast.so
  ```
- **Lean 4.35.0** via [elan](https://github.com/leanprover/elan) (optional, required to re-check `CollatzFormal` proofs locally; `leanprover/lean4:v4.35.0`)

### Run CLI Summary
Run from the parent directory containing `collatz_analysis/`:
```bash
python -m collatz_analysis.cli --summary
python -m collatz_analysis.cli --trajectory 27
```

### Build & Audit Lean 4 Proofs
```bash
cd collatz_analysis
lake build
```
Or audit all `957` theorems programmatically via `#print axioms` from Python:
```bash
python -c "from collatz_analysis import verify_lean4_kernel_proofs; print(verify_lean4_kernel_proofs())"
```

### Run Full Unit Test Suite
```bash
python -W error -m unittest discover -s collatz_analysis/tests -v
```
