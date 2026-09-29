-- Prove2me | solution 1 for SymmetryBreakingCost.isolationCost_isLeast
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:05:12.928508+00:00
-- url     : https://prove2.me/submissions/e39324cc-a2a2-4ba1-8e4a-afeca6abd161

-- Sol generated from Novelty/SymmetryBreakingCostFactoring.lean
import Mathlib
import Definitions.Def_Novelty_SymmetryBreakingCostFactoring
import Theorems.Thm_SymmetryBreakingCost_exists_isolating_battery
import Theorems.Thm_SymmetryBreakingCost_qsig_eq_of_bits

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






/-- **Information-theoretic lower bound.**  A tuple of `k` queries whose answers lie in a finite
alphabet `β` cannot separate more than `(card β) ^ k` candidates: if `|S|` exceeds that, two
distinct candidates are confused. -/
theorem info_lower_bound {β : Type*} [Fintype β] [DecidableEq β] (S : Finset ℕ) {k : ℕ}
    (f : ℕ → Fin k → β) (hk : Fintype.card β ^ k < S.card) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ f p = f q := by
  classical
  have hcard : (Finset.univ : Finset (Fin k → β)).card < S.card := by
    simpa [Finset.card_univ] using hk
  exact Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard (fun x _ => Finset.mem_univ _)






/-! ## 3.  The symmetric side: `N` alone prunes nothing -/





/-! ## 4.  The asymmetric quantum readout -/




open SymmetryBreakingCost in
theorem solution(S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) :
    IsLeast (IsolationCost S) (Nat.clog 2 S.card) := by
  classical
  constructor
  · exact exists_isolating_battery S hS (Nat.le_pow_clog (by norm_num) _)
  · rintro k ⟨a, hadm, hiso⟩
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    by_contra hcon
    push_neg at hcon
    obtain ⟨p, hp, q, hq, hpq, hfeq⟩ :=
      info_lower_bound (β := Bool) S (fun r i => decide (J(a i | r) = 1))
        (by simpa using hcon)
    refine hpq (hiso hp hq (qsig_eq_of_bits hadm hp hq (fun i => ?_)))
    have := congrFun hfeq i
    simpa using this
