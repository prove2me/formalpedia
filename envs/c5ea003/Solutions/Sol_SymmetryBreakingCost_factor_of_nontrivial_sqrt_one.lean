-- Prove2me | solution 1 for SymmetryBreakingCost.factor_of_nontrivial_sqrt_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:05:12.411926+00:00
-- url     : https://prove2.me/submissions/1f09e52f-da94-475c-b0da-0dfdf7477a91

-- Sol generated from Novelty/SymmetryBreakingCostFactoring.lean
import Mathlib
import Definitions.Def_Novelty_SymmetryBreakingCostFactoring

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












/-! ## 3.  The symmetric side: `N` alone prunes nothing -/





/-! ## 4.  The asymmetric quantum readout -/




open SymmetryBreakingCost in
theorem solution(N : ℕ) (x : ℤ) (hN : 1 < N) (hsq : (N : ℤ) ∣ x ^ 2 - 1)
    (h1 : ¬(N : ℤ) ∣ x - 1) (h2 : ¬(N : ℤ) ∣ x + 1) :
    Int.gcd (x - 1) N ∣ N ∧ 1 < Int.gcd (x - 1) N ∧ Int.gcd (x - 1) N < N := by
  set d : ℕ := Int.gcd (x - 1) N with hd
  have hdvdN : (d : ℕ) ∣ N := Int.natCast_dvd_natCast.mp (by
    simpa using Int.gcd_dvd_right (a := x - 1) (b := (N : ℤ)))
  have hdvdx : (d : ℤ) ∣ x - 1 := Int.gcd_dvd_left (x - 1) (N : ℤ)
  have hne1 : d ≠ 1 := by
    intro h
    have hcop : IsCoprime (x - 1) (N : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr h
    have hprod : (N : ℤ) ∣ (x - 1) * (x + 1) := by
      have : (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
      rw [this]; exact hsq
    exact h2 (hcop.symm.dvd_of_dvd_mul_left hprod)
  have hneN : d ≠ N := by
    intro h
    exact h1 (by rw [← h]; exact hdvdx)
  refine ⟨hdvdN, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos d with h | h
    · exfalso
      have : (N : ℕ) = 0 := Nat.eq_zero_of_zero_dvd (h ▸ hdvdN)
      omega
    · omega
  · exact lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdvdN) hneN
