-- Prove2me | solution 1 for ForkPinning.mutualInfo_lt_entropy_of_not_determines
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:04:15.967661+00:00
-- url     : https://prove2.me/submissions/596765d8-40e1-499b-8b64-bc454e3fc3ad

-- Sol generated from Probability/ForkPinningCore.lean
import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Theorems.Thm_ForkPinning_mutualInfo_le_entropy
import Theorems.Thm_ForkPinning_pinned_iff_determines
/-
# Fork pinning: a finite information-theoretic core

This file develops, from scratch, the small amount of finite information theory needed to
state and prove the **fork-pinning criterion**:

> a binary "fork" (a two-valued statistic of a Frobenius element) is congruence-pinned by a
> Dirichlet character exactly when it factors through the abelianization of the Galois group.

The probabilistic model is the uniform measure on a finite type `Ω` (which, in the arithmetic
application, is the Galois group of the splitting field; Chebotarev equidistribution turns
"a random prime" into "a uniformly random Frobenius element").

Main results:

* `ForkPinning.negMulLog_sum_le` / `negMulLog_sum_lt` : super-additivity of `x ↦ -x log x`
  on non-negative families, with the strict form.
* `ForkPinning.entropy_le_entropy_joint` : `H X ≤ H (X, Y)` (conditional entropy is non-negative).
* `ForkPinning.pinned_iff_determines` : `I(X;Y) = H Y ↔ X determines Y`  — the pinning criterion.
* `ForkPinning.mutualInfo_le_entropy` : `I(X;Y) ≤ H Y`.
* `ForkPinning.mutualInfo_nonneg` : `0 ≤ I(X;Y)` (Gibbs / sub-additivity of entropy).
* `ForkPinning.mutualInfo_eq_zero_of_indep` : independence ⇒ flat fork.
* `ForkPinning.mutualInfo_const_left` : a constant statistic carries no information
  (the "within-face fork is flat" mechanism).
-/


open ForkPinning

open Finset Real

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]
variable {κ β : Type*} [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β]

/-! ## Basic definitions: uniform measure, entropy, mutual information -/







/-! ## Elementary probability facts -/






/-! ## Super-additivity of `negMulLog` -/




/-! ## Conditional entropy is non-negative -/



/-! ## The pinning criterion -/







/-! ## Flatness -/







/-! ## Non-negativity of mutual information (Gibbs), with the equality case -/











/-! ## Capacity: the fork can learn at most `log |κ|` -/



/-! ## Conditional entropy: the quantitative pinned fraction -/







open ForkPinning in
theorem solution(X : Ω → κ) (Y : Ω → β)
    (h : ¬ Determines X Y) : mutualInfo X Y < H Y := by
  rcases lt_or_eq_of_le (mutualInfo_le_entropy X Y) with h' | h'
  · exact h'
  · exact absurd ((pinned_iff_determines X Y).mp h') h
