-- Prove2me | solution 1 for ForkPinning.determines_iff_factors
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:04:13.868698+00:00
-- url     : https://prove2.me/submissions/9f8c5148-92dd-4f2a-9da9-ca80dbeb106b

-- Sol generated from Probability/ForkPinningCore.lean
import Mathlib
import Definitions.Def_Probability_ForkPinningCore
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
omit [Nonempty Ω] [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β] in
theorem solution[Inhabited β] (X : Ω → κ) (Y : Ω → β) :
    Determines X Y ↔ ∃ ψ : κ → β, Y = ψ ∘ X := by
  classical
  constructor
  · intro h
    refine ⟨fun k => if hk : ∃ ω, X ω = k then Y hk.choose else default, ?_⟩
    funext ω
    have hk : ∃ ω', X ω' = X ω := ⟨ω, rfl⟩
    simp only [Function.comp_apply, dif_pos hk]
    exact (h hk.choose ω hk.choose_spec).symm
  · rintro ⟨ψ, rfl⟩ ω ω' hω
    simp [Function.comp_apply, hω]
