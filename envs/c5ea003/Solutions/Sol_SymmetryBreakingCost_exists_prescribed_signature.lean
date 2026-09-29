-- Prove2me | solution 1 for SymmetryBreakingCost.exists_prescribed_signature
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:57:52.011967+00:00
-- url     : https://prove2.me/submissions/d1c120b6-8072-404b-900f-c1d84cd02eb3

-- Sol generated from Novelty/SymmetryBreakingCostFactoring.lean
import Mathlib
import Definitions.Def_Novelty_SymmetryBreakingCostFactoring
import Theorems.Thm_SymmetryBreakingCost_crt_finset

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


/-- The Jacobi symbol only depends on the numerator modulo the denominator. -/
theorem jacobiSym_congr {a b : ℤ} {n : ℕ} (h : (n : ℤ) ∣ a - b) : J(a | n) = J(b | n) := by
  have hm : a ≡ b [ZMOD (n : ℤ)] := Int.ModEq.symm (Int.modEq_iff_dvd.mpr h)
  rw [jacobiSym.mod_left a, jacobiSym.mod_left b, hm]

/-! ## 1.  Independence of quadratic signatures -/


/-! ## 2.  Batteries, signatures, and the isolation cost -/












/-! ## 3.  The symmetric side: `N` alone prunes nothing -/





/-! ## 4.  The asymmetric quantum readout -/




open SymmetryBreakingCost in
theorem solution(S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2)
    (e : ℕ → Bool) : ∃ x : ℤ, ∀ p ∈ S, J(x | p) = if e p then 1 else -1 := by
  classical
  have H : ∀ p : ℕ, ∃ z : ℤ, p.Prime → p ≠ 2 → J(z | p) = if e p then 1 else -1 := by
    intro p
    by_cases hep : e p
    · exact ⟨1, fun _ _ => by simp [hep]⟩
    · by_cases hp : p.Prime
      · by_cases hp2 : p = 2
        · exact ⟨1, fun _ h => absurd hp2 h⟩
        · haveI : Fact p.Prime := ⟨hp⟩
          have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
          obtain ⟨y, hy⟩ := FiniteField.exists_nonsquare (F := ZMod p) hchar
          exact ⟨(y.val : ℤ), fun _ _ => by
            simpa [hep] using ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mpr (by simpa using hy)⟩
      · exact ⟨1, fun h => absurd h hp⟩
  choose b hb using H
  have hcop : (S : Set ℕ).Pairwise Nat.Coprime := fun x hx y hy hxy =>
    (Nat.coprime_primes (hS x hx).1 (hS y hy).1).mpr hxy
  obtain ⟨x, hx⟩ := crt_finset S hcop b
  refine ⟨x, fun p hp => ?_⟩
  rw [jacobiSym_congr (hx p hp)]
  exact hb p (hS p hp).1 (hS p hp).2
