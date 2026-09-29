-- Prove2me | Theorems.Thm_ForkPinning_entropy_congr_equiv
-- name    : ForkPinning.entropy_congr_equiv
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:35:50.759311+00:00
-- url     : https://prove2.me/theorems/630daf2d-8110-4a2a-8d0f-275d28191a49
-- title:
--   Entropy is invariant under relabelling the value type by a bijection.
-- statement:
--   Entropy is invariant under relabelling the value type by a bijection.
--
--   ```lean
--   theorem ForkPinning.entropy_congr_equiv{κ' : Type*} [Fintype κ'] [DecidableEq κ'] (e : κ ≃ κ')
--       (X : Ω → κ) : H (fun ω => e (X ω)) = H X := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/ForkPinningCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/ForkPinningCore.lean#L350

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







/-! ## Flatness -/






omit [Nonempty Ω] in

theorem ForkPinning.entropy_congr_equiv{κ' : Type*} [Fintype κ'] [DecidableEq κ'] (e : κ ≃ κ')
    (X : Ω → κ) : H (fun ω => e (X ω)) = H X := by sorry
