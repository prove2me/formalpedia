-- Prove2me | solution 1 for SymmetryBreakingCost.isolation_cost_le_of_le_four_pow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:07:12.497988+00:00
-- url     : https://prove2.me/submissions/c2681d47-1e70-46c5-8c94-6ff5764924bd

-- Sol generated from Novelty/SymmetryBreakingCostFactoring.lean
import Mathlib
import Definitions.Def_Novelty_SymmetryBreakingCostFactoring
import Theorems.Thm_SymmetryBreakingCost_exists_isolating_battery
import Theorems.Thm_SymmetryBreakingCost_isolationCost_isLeast

/-!
# The symmetry-breaking cost of factoring, measured

Let `N` be an odd semiprime and let `S` be the set of candidate prime factors (say, the odd
primes `p` with `p² ≤ N`).  A *battery* is a finite tuple `a : Fin k → ℤ` of test integers.
Two things can be measured with such a battery.

* **Asymmetric (oracle) data.**  An oracle answering with the *Legendre* symbols
  `[(a i | p₀)]` of the hidden factor `p₀`.  The signature `qsig a p = (J(a i | p))ᵢ` is then a
  fingerprint of a candidate, and isolating `p₀` costs exactly as many queries as the
  information-theoretic minimum `⌈log₂ |S|⌉`.
* **Symmetric (public) data.**  The Jacobi symbols `[(a i | N)]` computable from `N` alone.
  These prune *nothing*: every candidate `r` admits a compensating partner making it consistent
  with the whole battery.

The gap between the two is the "symmetry-breaking cost".  This file makes all three sides of
that statement into theorems.

## Main results

* `exists_prescribed_signature` (independence / CRT surjectivity): for any finite set `S` of
  distinct odd primes and any prescribed sign pattern `e : ℕ → Bool` there is a single integer
  `x` with `J(x | p) = ±1` according to `e p`, simultaneously for all `p ∈ S`.  The Legendre
  signatures of distinct primes are completely unconstrained by one another.
* `exists_isolating_battery`: if `|S| ≤ 2 ^ k` there is an admissible battery of size `k` whose
  signature map is injective on `S` — `k` queries isolate every candidate.
* `info_lower_bound`: no `k`-tuple of queries with answers in a finite alphabet `β` can separate
  more than `(card β) ^ k` candidates.
* `isolationCost_isLeast`: **the exact measurement.**  The set of achievable battery sizes has
  least element `Nat.clog 2 |S|`, i.e. the isolation cost is exactly `⌈log₂ |S|⌉`.
* `isolation_cost_le_of_le_four_pow`: for candidates below `√N` this cost is at most `½ log₂ N`.
* `factor_of_isolated`: an isolated candidate that divides `N` yields a nontrivial factorisation.
* `zero_pruning`, `compensating_partner`, `unboundedly_many_survivors`: the symmetric battery
  `[(a i | N)]` eliminates no candidate whatsoever.
* `factor_of_nontrivial_sqrt_one`, `factor_of_even_order`: the *asymmetric* readout of Shor's
  algorithm (an element of even multiplicative order whose half-power is not `±1`) converts into
  a nontrivial factor by a gcd — the quantum payment for the same symmetry breaking.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the quadratic-residue signature of a prime is "generic": knowing the
signatures of all other primes tells you nothing about `p₀`'s.  If true, the signature map is a
perfect binary code on the candidate set and the isolation cost must equal `⌈log₂ |S|⌉` exactly,
with no slack in either direction.

Experiment (Experimenter): computed in `ComputationalEvidence.md`.  For the candidate sets of
`N = 3149 = 47·67`, `N = 10403 = 101·103` and `N = 1000003·1000033` truncated to the primes
below `√N`, greedy batteries of size `⌈log₂ π(√N)⌉` separated all candidates in every trial,
and no battery of size `⌈log₂ π(√N)⌉ - 1` ever did (pigeonhole).  Ratio (queries used) /
`log₂ π(√N)` stayed in `[1, 1.03]`.

Analysis (Analyst): both halves are structural, not statistical.  The upper bound is CRT:
sign patterns of distinct primes are independent, so the signature map can realise *any*
injection `S ↪ {±1}^k`.  The lower bound is pigeonhole on the answer alphabet.  Hence the
measurement `⌈log₂ |S|⌉` is exact, not asymptotic.

Critique (Critic): the lower bound must be stated for the alphabet actually used.  A Jacobi
symbol has three values, and a `0` answer is itself a factor disclosure; we therefore define
`Admissible` batteries (no `0` answers) for the exact `log₂` statement and record the general
ternary bound `info_lower_bound` separately.  No theorem below is vacuous: `isolationCost_mem`
exhibits the battery, and `zero_pruning` is proved for arbitrary candidates.
-/

open SymmetryBreakingCost

open Finset
open scoped NumberTheorySymbols

/-! ## 0.  Chinese remainder input -/



/-! ## 1.  Independence of quadratic signatures -/


/-! ## 2.  Batteries, signatures, and the isolation cost -/









/-- Restated: `k` queries suffice **iff** `2 ^ k` is at least the number of candidates. -/
theorem mem_isolationCost_iff (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (k : ℕ) :
    k ∈ IsolationCost S ↔ S.card ≤ 2 ^ k := by
  constructor
  · intro hk
    have := (isolationCost_isLeast S hS).2 hk
    exact (Nat.clog_le_iff_le_pow (by norm_num)).mp this
  · exact fun h => exists_isolating_battery S hS h



/-! ## 3.  The symmetric side: `N` alone prunes nothing -/





/-! ## 4.  The asymmetric quantum readout -/




open SymmetryBreakingCost in
theorem solution(N k : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (hsq : ∀ p ∈ S, p * p ≤ N) (hN : N ≤ 4 ^ k) :
    k ∈ IsolationCost S := by
  classical
  have hsqrt : Nat.sqrt N ≤ 2 ^ k := by
    have h4 : (4 : ℕ) ^ k = 2 ^ k * 2 ^ k := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
    calc Nat.sqrt N ≤ Nat.sqrt (2 ^ k * 2 ^ k) := Nat.sqrt_le_sqrt (h4 ▸ hN)
      _ = 2 ^ k := Nat.sqrt_eq _
  have hsub : S ⊆ Finset.Icc 3 (Nat.sqrt N) := by
    intro p hp
    obtain ⟨hprime, hne2⟩ := hS p hp
    refine Finset.mem_Icc.mpr ⟨?_, Nat.le_sqrt.mpr (hsq p hp)⟩
    have h2 := hprime.two_le
    omega
  have hcard : S.card ≤ 2 ^ k := by
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    omega
  exact (mem_isolationCost_iff S hS k).mpr hcard
