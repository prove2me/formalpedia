-- Prove2me | solution 1 for ForkPinning.mutualInfo_le_log_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:10:39.659505+00:00
-- url     : https://prove2.me/submissions/1e81e25c-1c4b-49ab-8b9a-9871e47e07a9

-- Sol generated from Probability/ForkPinningCore.lean
import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Theorems.Thm_ForkPinning_entropy_congr_equiv
import Theorems.Thm_ForkPinning_entropy_le_log_card
import Theorems.Thm_ForkPinning_mutualInfo_le_entropy
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
theorem solution(X : Ω → κ) (Y : Ω → β) :
    mutualInfo X Y ≤ Real.log (Fintype.card κ) := by
  have h1 : mutualInfo X Y ≤ H X := by
    have h2 : mutualInfo Y X ≤ H X := mutualInfo_le_entropy Y X
    have hswap : mutualInfo X Y = mutualInfo Y X := by
      unfold mutualInfo
      have hj : H (joint X Y) = H (joint Y X) := by
        have := entropy_congr_equiv (Ω := Ω) (Equiv.prodComm β κ) (joint Y X)
        rw [show (fun ω => (Equiv.prodComm β κ) (joint Y X ω)) = joint X Y from rfl] at this
        rw [this]
      rw [hj]; ring
    rw [hswap]; exact h2
  exact le_trans h1 (entropy_le_log_card X)
