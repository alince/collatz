# Collatz Conjecture: 2-Adic Dynamics, Unconditional $m$-Cycle Elimination ( $m \le 99$ ), & Pure-Kernel Lean 4 Proofs

A formal-methods and computational number-theory research suite combining **Lean 4** pure-kernel theorem proving (zero external dependencies, zero `sorry`, zero `native_decide`, zero custom axioms), a **zero-dependency Python** analytical/verification library, and a **portable C23** native 2-adic Hensel search kernel (`_hensel_fast.c`).

For full derivations and theorem-by-theorem mathematical exposition, see [`MATHEMATICAL_FINDINGS.md`](MATHEMATICAL_FINDINGS.md), and for the living whole-space paradigm taxonomy and dead-end registry see [`PROOF_SPACE_LEDGER.md`](PROOF_SPACE_LEDGER.md).

---

## What Was Proved

All claims explicitly track their hypotheses: pure algebraic, 2-adic, Diophantine, and equivalence theorems are proved **unconditionally** inside Lean 4; cycle non-existence results above $N_0 = 2^{71}$ explicitly assume Laurent–Mignotte–Nesterenko linear forms in logarithms (`BakerLMNPowerBound`) and Barina's (2025) computational convergence verification threshold (`BarinaThreshold (2 ^ 71)`).

### 1. Unconditional Positive $m$-Cycle Elimination Through $1 \le m \le 99$
- **Pure Lean 4 Kernel Pipeline ( $1 \le m \le 93$ + higher-weight $m = 94..96$ tails):** Assuming only `BarinaThreshold (2 ^ 71)` and `BakerLMNPowerBound`, `CollatzFormal/HenselBridge93To96.lean` proves `no_nontrivial_spiral_cycles_1_to_93` end-to-end inside the Lean 4 kernel with zero external trust gap, plus `u >= 2` at $m = 94$, `u >= 3` at $m = 95$, and `u >= 4` at $m = 96$.
- **C23 + Lean 4 Hybrid Frontier ( $1 \le m \le 99$ ):** Extending beyond Steiner ( $m = 1$ ) and Hercher ( $m \le 91$ ), Theorem 33 (`prove_m99_unconditional_hensel_frontier` in `goal_extensions.py`) eliminates all positive spiral $m$-cycles for **$1 \le m \le 99$** at $N_0 = 2^{71}$, with **all newly discovered $m = 97..99$ arithmetic survivors ( $19{,}175$ pairs in `CollatzFormal/Survivors97To99A`..`J.lean`, alongside $8{,}139$ pairs in `CollatzFormal/Survivors.lean`) independently verified to drop $\le 2^{71}$ in the Lean 4 kernel via `by decide`** (`m97_to_99_hensel_survivor_drop_universal`).

### 2. Canonical Conjecture Equivalences, First-Hit Generator Bijection & Mod $373{,}248$ Sieve (`Core.lean`, `BoostMechanisms.lean`, `CSFullConjecture.lean`, `CSWave3Synthesis.lean`)
Proved inside the Lean 4 kernel (`↔` iff, with zero custom axioms):
- Equivalence of `CollatzConjectureStandard` to the compressed Terras map, strict stopping-time descent, the two-barrier conjunction `NoDivergentPositiveOrbits ∧ NoNontrivialPositiveCycles`, and side-condition-free One-Equation Diophantine solvability (`collatz_iff_one_equation_diophantine`).
- Constructive all-weight ( $\forall w \ge 1$ ) $3$-adic totient lifting $2^{2 \cdot 3^{w-1}} = 1 + 3^w k_w$ with $k_w \bmod 3 = 1$, exact $(\mathbb{Z}/3^w\mathbb{Z})^\times$ Hensel discrete-logarithm bijection (`dlog2ModPow3_bijective`), universal odd-start escape (`collatzIter_odd_nondiv3_universal`), total side-condition-free backward predecessor operator `exactBackwardQuotient`, and the exact non-descending logarithmic suffix-shift bottleneck $2^{\text{canonicalSuffixShift}(u, x)} < 3^{w(u)}$ (`non_descending_contraction_forces_log_shift_arc`).
- Arbitrary-depth inverse Syracuse forest collapse (`odd_forest_collision_collapses_to_core_contraction`), horizon-supercritical core prefix splitting (`horizon_supercritical_core_reduction_at_n`), and all-weight $2^{w\sb 1}$-cancellation + dyadic mod $512$ sieving shrinking minimal-counterexample survival from $131/1296 \approx 10.1080\%$ down to **$10{,}314 / 373{,}248 = 191 / 6{,}912 \approx 2.7633\%$** (`survivingMod373248_count_eq_10314`), augmented by infinite pairwise-disjoint $\forall k \ge 2$ dyadic (`infinite_dyadic_entry_merger_excluded_family`) and $\forall k \ge 3$ triadic (`infinite_triadic_backward_merger_excluded_family`, with $r_k \bmod 729 = 361$ ) excluded progressions.
- Total $x = 1$ convergent odd generator `exactBackwardQuotient 1 u q` (`one_generator_pos_odd_and_reaches_one`, mapping $\lbrack \text{true}\rbrack \mapsto (4^{q+1}-1)/3$ ), canonical unique first-hit bijection onto all convergent odd $n > 1$ (`convergent_odd_gt1_iff_unique_first_hit_pair`), and forward-iteration-free range equivalences `CollatzConjectureStandard ↔ Mod373248OneGeneratorRangeProp ↔ Mod373248UniqueFirstHitRangeProp` (`collatz_standard_iff_mod373248_unique_first_hit_range`, confining witnesses to `true :: true :: tail` with $w \ge 3$ ).
- Wave 3 sharpened pure-`Nat` Brox cycle characterization (`no_nontrivial_cycles_iff_wave3_sharpened_brox_obstruction` & `unified_wave3_master_collatz_equivalences`): combines the $8/96 = 1/12$ cycle-minimum sieve, $(21, 22)$ exponent band, $2$-adic LTE squeeze $2^a \mid (3^w - 1) \implies 2^a \le 4w$, sharp $1$-block GCD lock $D \mid \gcd(2^{a\sb 1} - 1,\; 3^{w\sb 1} - 2^{w\sb 1})$ eliminating all $q\sb 0 = 3^r$ and forcing $q\sb 0 \ge 17,\; w\sb 1 \ge 13,\; a\sb 1 \ge 8,\; x\sb 0 \bmod 96 \in \lbrace 31, 95\rbrace$ (`one_block_no_pow3_quotient_and_q0_ge_17`), Hercher $1$-block non-convergent partner (`one_block_cycle_has_smaller_nonconvergent_partner`), and complete $2$-block reduction (`no_two_block_cycles_iff_one_block_and_primitive_brox` & `subexponential_cubic_gap_eliminates_1_and_2_block_cycles` via `SubexponentialCubicGapProp`).

### 3. Structural Number-Theory, Algebraic & CS Obstruction Results
- **2-Adic Homeomorphism, Koopman Fibers & `bbchallenge` Regular Barrier:** Measure-preserving 2-adic parity bijection, exact Cramér large-deviation rate $1 - H\sb 2(\log\sb 3 2)$, all-weight Ramanujan primitive-character orthogonality and Koopman primitive-fiber annihilation (`koopman_primitive_fiber_annihilation`), Myhill–Nerode $2^w$ (`binGapWord_pairwise_myhill_nerode_distinguished`) and $3^w$ (`mnWitnessFamily_card_pow3_and_pairwise_distinguished`) witness families on `IsValidOneEquationWord`, and universal $\forall N \ge 1$ deterministic finite automaton refutation (`no_finite_dfa_recognizes_one_equation_language`).
- **Universal LP, Matrix-Interpretation, Radial Hardy/Bergman, Presburger & Laurent-Monomial Obstructions (`CSFullConjecture.lean`, `CSWave3Synthesis.lean`, `Wave4WholeSpace.lean`):** Formal impossibility of bounded-modulus $\pmod{2^A 3^B}$ rational-potential cycle certificates (`bounded_modulus_rational_potential_obstruction`), $d=1$ affine natural, $\forall d \ge 1$ arctic (`arctic_quadratic_height_impossibility`), $d=2$ top-left-monotone upper-triangular natural (`d2_upper_triangular_natural_impossibility`), and $\forall d \ge 1$ coordinatewise-monotone upper-triangular natural (`all_dim_coord_monotone_upper_triangular_impossibility`, sharp against `sub6_admits_2d_top_left_monotone_upper_triangular_cert`) matrix termination proofs on mixed $(2,3)$ Collatz rewriting, monotone-per-residue $\Phi(x, x \bmod 2^A 3^B)$ potentials inside `IsSurvivingMod373248Class` (`self_congruent_syracuse_pumping_mod373248_obstruction`), $\forall r \ge 1$ radial Hardy and decaying rational/weighted Bergman transfer-operator contractions for Berg–Meinardus (`berg_meinardus_radial_hardy_norm_gt_one`, `berg_meinardus_rational_and_bergman_norm_gt_one`), $\forall N_0, P \ge 1$ two-sided and one-sided forward-closed Presburger/semilinear basin-separating invariants (`presburger_invariant_separator_collapse`, `one_sided_presburger_infinite_forward_hits_one`), $\forall r \ge 1$ eventually strictly increasing ranking functions (`monotone_ranking_function_r_step_impossibility`), and arbitrary-sign $(\alpha, \beta, \gamma) \in \mathbb{Z}^3$ Laurent $(2,3)$-adic valuation monomials on Syracuse steps (`syracuse_laurent_valuation_monomial_impossibility`).
- **Carry-Coupled $\forall m \ge 1$ Spiral Resultant Lock, Antipodal & Equal-Even Cycle Exclusions, Sharp $(w \ge 6,\; |u| \ge 8)$ `exactBackwardQuotient` Floors, & Three Solvable Cousin Benchmarks (`Wave4WholeSpace.lean`, `Wave5WholeSpace.lean`, `Wave6WholeSpace.lean`, `PROOF_SPACE_LEDGER.md`, `witness_bank.json`):** Unconditional $\forall m \ge 1$ `m`-block affine-carry bridge (`broxSpiralCarry_eq_affineCarry_universal`), carry-determinant resultant elimination $2^{a_j+w_{j+1}} H_{j+1} = 3^{w_j} H_j + D(2^{a_j}-1)$, single-block divisibility propagation $D \mid H_0 \implies \forall j < m, D \mid H_j$, global Mersenne quotient GCD lock $\gcd_j q_j \mid \gcd_j (2^{a_j}-1)$, and cyclic mod-3 bi-implication $3 \mid q_{j+1} \iff 2 \mid a_j$ (`m_block_brox_resultant_and_quotient_locks`, `m_block_cycle_induces_brox_quotients`), 1-block even-even impossibility (`one_block_even_even_impossibility`), 1-block and shared-Mersenne $m$-block antipodal-order divisor locks (`one_block_antipodal_order_divisor_exclusion`, `m_block_antipodal_shared_mersenne_parity_and_mod3_lock`), 2-block single-Mersenne propagation and equal-even-run cone exclusion (`two_block_shared_mersenne_propagation_and_equal_even_exclusion`), pure-integer Schneider–Laurent 2-logarithm determinant gap divisibility (`laurent_interp_resonant_row_collapse_and_gap_divisibility`), non-radial Berg–Meinardus preimage superharmonicity meta-theorems plus periodic/valuation and universal 6-variable coupled-core rational impossibility (`preimage_superharmonic_rational_eliminates_all_cycles`, `berg_meinardus_periodic_valuation_weight_impossibility`, `berg_meinardus_coupled_core_rational_weight_impossibility`), $\forall d \ge 1$ non-upper-triangular coordinatewise-monotone, zero-diagonal $d = 2$ `sub6 ∪ {R1}`, and $\forall d \ge 1$ bipartite zero-diagonal swap matrix collapses (`all_dim_coord_monotone_non_triangular_impossibility`, `zero_diag_upper_tri_2d_r1_sub6_impossibility`, `bipartite_zero_diag_swap_r1_impossibility_all_dim`), $\forall L \ge 1$ multi-term Laurent valuation impossibility on both single Syracuse steps and variable-horizon spiral block-returns (`syracuse_multiterm_laurent_valuation_impossibility`, `spiral_block_return_multiterm_laurent_impossibility`), coupled $q$-ray dyadic pinning & triadic `Fin 729` bijection, sharp $(w \ge 6,\; |u| \ge 8)$ pruning, cross-ray disjointness, exact $11 + 16 = 27$ surviving $\bmod 512$ prefix partition, automatic `w ≥ 7` $2^{L-10}$ fiber uniformity & prefix characterization, and quantitative logarithmic zero-density bounded-length non-covering (`mod373248_ray_dyadic_pinning_and_triadic_bijection`, `collatz_standard_iff_mod373248_unique_first_hit_len_ge_eight`, `first_hit_ray_global_disjointness_and_q0_necessity`, `mod512_surviving_prefix_partition_cert`, `surviving_mod512_nine_prefix_auto_weight_and_characterization`, `bounded_length_ray_logarithmic_counting_zero_density`), and three non-trivial solvable $(3x+1)$-cousin benchmarks $T_\diamond$ (`cousin_diamond_global_convergence`), $T_{\diamond 2}$ (`cousin_diamond2_global_convergence`), and $T_{\diamond 3}$ (`cousin_diamond3_global_convergence`, `cousin_diamond3_multiterm_laurent_impossibility`, defeating ALL fixed-step $L$-term Laurent valuation sums while converging globally within $k \le (x+1)^3 + (x+1)^5$ steps via variable-horizon Cone-4 block-return).
- **Diophantine & $p$-Adic Cycle Classifications:** Catalan–Mihăilescu unit denominators ( $\lvert 2^k - 3^w \rvert = 1$ ), $N_0$-free $2$- and $3$-cycle classifications over $\mathbb{Z}$, $S$-integer cycles in $\mathbb{Z}\lbrack 1/30\rbrack$, and complete classification of $\lvert 2^k - 3^w \rvert = 5^e$.
- **Mandatory $3 \times 3$ Counter-Model & CEGAR Audit (`cs_cegar_redteam.py`):** Candidate mechanisms are tested against three known obstructions— $\mathbb{Q}\sb{(2)}^+$ cycles ( $19/5, 29/5, 251/13, 287/13$ ), $\mathbb{Z}^-$ cycles ( $-1, -5, -17$ ), and $5n+1$ positive cycles ( $5, 13, 17$ )—to catch unsound generalizations early.

### 4. Lean 4.35.0 Kernel Audit Summary
- **Toolchain:** `leanprover/lean4:v4.35.0` (zero external Lake dependencies).
- **Files:** `55` `.lean` files (`CollatzFormal.lean` + `54` modules under `CollatzFormal/`).
- **Verified Theorems/Lemmas:** `1,593` declarations compiled cleanly with `--wfail`, zero warnings, zero `sorryAx`, zero `native_decide`, and zero custom axioms (`550` theorems completely axiom-free `[]`; all remaining theorems rely only on Lean's standard foundational axioms `Classical.choice`, `Quot.sound`, `propext`).

---

## What Remains Open (Scope & Honest Boundaries)

- **The full Collatz Conjecture is NOT proved:** `CollatzConjectureStandard`, `NoDivergentPositiveOrbits`, `NoNontrivialPositiveCycles`, `Mod373248UniqueFirstHitLenGeEightProp`, and `SubexponentialCubicGapProp` remain open conjectures.
- **Global `↔` equivalences do not reduce hardness:** Theorems such as `CollatzConjectureStandard ↔ Mod373248UniqueFirstHitLenGeEightProp` and `NoNontrivialPositiveCycles ↔ ¬ IsWave3SharpenedBroxWitness` are exact number-theoretic restatements (backed by sharp forward pruning `w ≥ 6, |u| ≥ 8` at `y = 184,111`), not solutions to global surjectivity or cycle non-existence.
- **What Waves 1–6 actually established:** Rather than closing the global conjecture, Waves 1–6 (`CSFullConjecture.lean`, `CSWave3Synthesis.lean`, `Wave4WholeSpace.lean`, `Wave5WholeSpace.lean`, `Wave6WholeSpace.lean`) provide (1) **formal "no-go" impossibility proofs** ruling out DFAs (`∀ N ≥ 1`), coordinatewise-monotone matrix interpretations (`∀ d ≥ 1`, even non-triangular), zero-diagonal $d = 2$ `sub6 ∪ {R1}` upper-triangular interpretations, and $\forall d \ge 1$ bipartite zero-diagonal swap interpretations, bounded-modulus $\pmod{2^A 3^B}$ LP/Lyapunov potentials, radial Hardy/Bergman, periodic/valuation, and 6-variable coupled-core rational Berg–Meinardus preimage weights, two-sided and one-sided Presburger invariants (`∀ N₀, P ≥ 1`), bounded-length `q`-ray coverings (`∀ L_max`, asymptotic natural density $0$), and arbitrary $L$-term (`∀ L ≥ 1`) Laurent valuation sums on both single Syracuse steps and variable-horizon spiral block-returns (plus computational falsifications of direct Rudolph–Host rigidity, additive 1D/2D Padé/Beukers–Rhin integrals, and fixed-grid Laurent determinants without zero-multiplicity in `witness_bank.json`); (2) **three solved non-trivial $(3x+1)$-cousin benchmarks** (`T_diamond`, `T_diamond2`, `T_diamond3`) where DFAs, bounded-modulus LPs, 1-term valuation monomials, and ($T_{\diamond 3}$) ALL $L$-term fixed-step Laurent valuation sums provably fail; and (3) **zero-axiom forward infrastructure** (`∀ w ≥ 1` 3-adic Hensel discrete-log & $x=1$ first-hit bijection, cross-ray disjointness, $11 + 16 = 27$ automatic `w ≥ 7` prefix-fiber uniformity, coupled $q$-ray `382/729` triadic covering, `∀ m ≥ 1` spiral carry resultants & shared-Mersenne antipodal locks, 1-block antipodal and 2-block equal-even cone exclusions, and pure-integer Schneider–Laurent gap divisibility toward `SubexponentialCubicGapProp`).

---

## How It Was Done

1. **Rational-Logarithm Slabs & $q\sb{43}$ Lattice Confinement:** Upper convergents/semiconvergents of $\log_2 3$ (specifically $p\sb{43}/q\sb{43}$ with $q\sb{43} = 205{,}632{,}218{,}873{,}398{,}596{,}256$ ) pin any hypothetical cycle's total odd/even counts $(W, K)$ to narrow congruence strips and give monotone $u$-tail cutoffs ( $u\sb{\text{cut}} = 14, 15, 15$ at $m = 97, 98, 99$ ).
2. **Two-Vertex $(x\sb{(1)}, x\sb{(2)})$ Reciprocal-Budget Split & $4$-Shell De Morgan Climb:** For low multiplicity ( $u = 1$ ) at $m \in \lbrace 97, 98, 99\rbrace$, reciprocal-budget constraints $\sum 1/x_i$ are partitioned into dyadic $(x\sb{(1)}, x\sb{(2)})$ strips with $s\sb{\text{low}}$-stratified cutoffs and sorted-cycle dominance checks (showing `(99, 1)` bounds dominate `(97, 1)` and `(98, 1)`).
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
├── cs_lp_cycles.py                # Rational LP/Farkas cycle duals, 1/2-block Brox & GCD locks
├── cs_sat_lyapunov.py             # Mixed (2,3) SRS, matrix/DFA barriers, mod-373248 & infinite sieves
├── cs_forest_transfer.py          # All-w Hensel dlog, x=1 first-hit bijection & Koopman fibers
├── cs_cegar_redteam.py            # 3x3 adversarial counter-model & CEGAR obstruction auditor
├── formal_proofs.py               # Automated Lean 4 compiler & `#print axioms` audit harness
├── _hensel_fast.c                 # Portable C23 multi-step 2-adic Hensel acceleration library
├── MATHEMATICAL_FINDINGS.md       # Detailed mathematical documentation (Theorems 1-33 + Waves 1-6)
├── PROOF_SPACE_LEDGER.md          # Living whole-space proof paradigm taxonomy & barrier ledger
├── witness_bank.json              # Permanent self-improving adversarial witness bank
├── lakefile.lean                  # Lean 4 Lake build configuration
├── lean-toolchain                 # Lean toolchain pin (leanprover/lean4:v4.35.0)
├── lake-manifest.json             # Lake manifest (zero external dependencies)
├── CollatzFormal.lean             # Root Lean 4 umbrella module
├── CollatzFormal/                 # 54 Lean 4 submodules (Core, CSFullConjecture, CSWave3Synthesis, Wave4WholeSpace, Wave5WholeSpace, Wave6WholeSpace, Survivors*, HenselBridge*)
└── tests/
    ├── test_collatz.py            # Core Theorem 1-33 & Lean 4 audit suite
    ├── test_cs_lp_cycles.py       # Track 1 universal cycle sieve & LP obstruction tests
    ├── test_cs_sat_lyapunov.py    # Track 2 SRS/matrix, mod-373248 sieve & pumping tests
    ├── test_cs_forest_transfer.py # Track 3 all-w dlog, exact quotient & Koopman tests
    └── test_cs_cegar_redteam.py   # Track 4 adversarial 3x3 counter-model & CEGAR tests
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
Or audit all `1,593` theorems programmatically via `#print axioms` from Python:
```bash
python -c "from collatz_analysis import verify_lean4_kernel_proofs; print(verify_lean4_kernel_proofs())"
```

### Run Full Unit Test Suite
```bash
python -W error -m unittest discover -s collatz_analysis/tests -v
```
