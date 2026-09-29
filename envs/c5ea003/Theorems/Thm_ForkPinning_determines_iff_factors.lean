-- Prove2me | Theorems.Thm_ForkPinning_determines_iff_factors
-- name    : ForkPinning.determines_iff_factors
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:35:38.375759+00:00
-- url     : https://prove2.me/theorems/9197ee1a-b084-40a0-8b9a-ae7e8514860c
-- title:
--   Factoring through `X` is the same as being determined by `X`.
-- statement:
--   Factoring through `X` is the same as being determined by `X`.
--
--   ```lean
--   theorem ForkPinning.determines_iff_factors[Inhabited β] (X : Ω → κ) (Y : Ω → β) :
--       Determines X Y ↔ ∃ ψ : κ → β, Y = ψ ∘ X := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/ForkPinningCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/ForkPinningCore.lean#L269

-- Thm stub generated from Probability/ForkPinningCore.lean
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






omit [Nonempty Ω] [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β] in

theorem ForkPinning.determines_iff_factors[Inhabited β] (X : Ω → κ) (Y : Ω → β) :
    Determines X Y ↔ ∃ ψ : κ → β, Y = ψ ∘ X := by sorry
