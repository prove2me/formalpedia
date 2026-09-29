-- Prove2me | Theorems.Thm_EMLInformationGeometryDeepening_constant_feature_forces_fisher_degeneracy
-- name    : EMLInformationGeometryDeepening.constant_feature_forces_fisher_degeneracy
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:18:32.845097+00:00
-- url     : https://prove2.me/theorems/c188ca33-5b46-48d4-b7de-0f226b88551f
-- title:
--   Contrarian conclusion: when `g₁` is constant, the first coordinate vector is
-- statement:
--   Contrarian conclusion: when `g₁` is constant, the first coordinate vector is
--   always a nonzero null direction of the full three-parameter EML Fisher matrix.
--
--   ```lean
--   theorem EMLInformationGeometryDeepening.constant_feature_forces_fisher_degeneracy[Nonempty ι]
--       (g₁ g₂ : ι → ℝ) (c : ℝ) (hg₁ : ∀ i, g₁ i = c)
--       (θ : Fin 3 → ℝ) (hlog : ∀ i, 1 < θ 1 * g₂ i + θ 2) :
--       let e₁ : Fin 3 → ℝ := fun j => if j = 0 then 1 else 0
--       e₁ ≠ 0 ∧
--         (∑ j, ∑ k, e₁ j * emlFisher g₁ g₂ θ j k * e₁ k) = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/EMLInformationGeometryDeepening.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/EMLInformationGeometryDeepening.lean#L196

-- Thm stub generated from Probability/EMLInformationGeometryDeepening.lean
import Mathlib
import Definitions.Def_Probability_EMLInformationGeometryDeepening

/-!
# Exact nullspace geometry for finite exp-log models

This file deepens the finite EML analysis from a single common exponential scale to
an arbitrary feature `g₁`.  It proves a general Gram/nullspace theorem for Fisher
matrices, applies it to the three-parameter exp-log model

`exp(θ₁ g₁(x)) * log(θ₂ g₂(x) + θ₃)`,

and isolates the precise obstruction caused by a constant exponential feature.
The result is stronger than merely exhibiting a zero determinant: every null
Fisher direction is characterized pointwise as a vanishing centered directional
score.
-/

noncomputable section

open Finset
open scoped BigOperators

open EMLInformationGeometryDeepening

variable {ι : Type*} [Fintype ι]
variable {d : ℕ}

theorem EMLInformationGeometryDeepening.constant_feature_forces_fisher_degeneracy[Nonempty ι]
    (g₁ g₂ : ι → ℝ) (c : ℝ) (hg₁ : ∀ i, g₁ i = c)
    (θ : Fin 3 → ℝ) (hlog : ∀ i, 1 < θ 1 * g₂ i + θ 2) :
    let e₁ : Fin 3 → ℝ := fun j => if j = 0 then 1 else 0
    e₁ ≠ 0 ∧
      (∑ j, ∑ k, e₁ j * emlFisher g₁ g₂ θ j k * e₁ k) = 0 := by sorry
