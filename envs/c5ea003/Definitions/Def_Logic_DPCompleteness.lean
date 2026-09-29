-- Prove2me | Definitions.Def_Logic_DPCompleteness
-- name    : Logic_DPCompleteness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:52:49.22163+00:00
-- url     : https://prove2.me/theorems/e8a203c7-08b2-4d72-97a3-304115fb5f3c
-- title:
--   Aether Catalog definitions — Logic_DPCompleteness
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.DPCompleteness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/DPCompleteness.lean by skeleton subtraction
import Mathlib
/-
# Completeness of Dynamic Programming: every labelling is dominated by some DP run

This file develops, from scratch, a general theory of *layered dynamic programming*
(the Viterbi / Bellman shortest-path schema) over an arbitrary finite state space `S`
and an arbitrary linearly ordered cancellative additive monoid `W` of weights, and
proves the **completeness theorem**:

> every labelling `f : ℕ → S` is dominated by some DP run `g`, i.e. there is a `g`
> all of whose prefixes are DP-optimal and whose total score is at least that of `f`.

Together with the dual **soundness** statement (every DP run is an honest labelling whose
score is exactly the DP value) this gives an exactness theorem: the DP value function is
the greatest element of the set of achievable labelling scores.

We additionally prove
* the **Bellman optimality principle** (`IsDPRun` is inherited by every prefix of an
  end-optimal labelling),
* the **forward-backward decomposition** relating the forward value function to a
  backward value function at any intermediate stage,
* **monotonicity** of the value function in the specification.

Everything is stated for a general weight monoid, so it specialises simultaneously to
max-plus (longest path), min-plus (shortest path, by using the order dual), and
Viterbi-style probabilistic decoding.
-/


namespace Logic.DPCompleteness

/-! ## Generic `sup'` lemmas -/

section SupLemmas

variable {ι W : Type*} [LinearOrder W] [AddCommMonoid W] [AddLeftMono W]



end SupLemmas

/-! ## The DP specification -/

/-- A layered dynamic-programming specification: an initial weight for each state and a
stage-dependent transition weight. -/
structure DPSpec (S W : Type*) where
  /-- weight of starting in a given state -/
  init : S → W
  /-- `step i s t` is the weight of moving from state `s` at stage `i` to state `t` at
  stage `i + 1`. -/
  step : ℕ → S → S → W

namespace DPSpec

variable {S W : Type*} [AddCommMonoid W]

/-- The total score of the labelling `f` truncated at stage `n`. -/
def score (D : DPSpec S W) (f : ℕ → S) : ℕ → W
  | 0 => D.init (f 0)
  | (n + 1) => D.score f n + D.step n (f n) (f (n + 1))




section Value

variable [Fintype S] [Nonempty S] [LinearOrder W]

/-- The forward DP value function: `val D n s` is the best score of a labelling of stages
`0 … n` that ends in state `s`. -/
def val (D : DPSpec S W) : ℕ → S → W
  | 0, s => D.init s
  | (n + 1), t =>
      (Finset.univ : Finset S).sup' Finset.univ_nonempty (fun s => D.val n s + D.step n s t)



variable [AddLeftMono W]



/-! ## DP runs -/

/-- `IsDPRun D n f` says that the labelling `f` is a genuine run of the dynamic program up to
stage `n`: *every* prefix score is DP-optimal, i.e. `f` is produced by the DP recursion. -/
def IsDPRun (D : DPSpec S W) (n : ℕ) (f : ℕ → S) : Prop :=
  ∀ i ≤ n, D.score f i = D.val i (f i)



end Value

section Cancel

variable [Fintype S] [Nonempty S] [LinearOrder W] [IsOrderedCancelAddMonoid W]


end Cancel

/-! ## Existence of DP runs -/

section Existence

variable [Fintype S] [Nonempty S] [LinearOrder W] [IsOrderedCancelAddMonoid W]







end Existence

/-! ## Backward values and the forward–backward decomposition -/

section Backward

variable [Fintype S] [Nonempty S] [LinearOrder W] [AddLeftMono W]

/-- The backward DP value: `bval D k m s` is the best weight of `m` further transitions
starting from state `s` at stage `k`. -/
def bval (D : DPSpec S W) : ℕ → ℕ → S → W
  | _, 0, _ => 0
  | k, (m + 1), s =>
      (Finset.univ : Finset S).sup' Finset.univ_nonempty
        (fun t => D.step k s t + D.bval (k + 1) m t)




end Backward

/-! ## Monotonicity in the specification -/

section Monotone

variable [Fintype S] [Nonempty S] [LinearOrder W] [AddLeftMono W]



end Monotone

end DPSpec

end Logic.DPCompleteness


