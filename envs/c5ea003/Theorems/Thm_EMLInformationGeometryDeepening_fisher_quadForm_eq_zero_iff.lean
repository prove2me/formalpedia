-- Prove2me | Theorems.Thm_EMLInformationGeometryDeepening_fisher_quadForm_eq_zero_iff
-- name    : EMLInformationGeometryDeepening.fisher_quadForm_eq_zero_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:19:34.109615+00:00
-- url     : https://prove2.me/theorems/bdbf012a-aeaf-4794-be5e-77963ac261ff
-- title:
--   With full support, the Fisher nullspace consists exactly of directions whose
-- statement:
--   With full support, the Fisher nullspace consists exactly of directions whose
--   centered directional score vanishes at every sample.
--
--   ```lean
--   theorem EMLInformationGeometryDeepening.fisher_quadForm_eq_zero_iff(p : ι → ℝ) (s : ι → Fin d → ℝ)
--       (hp : ∀ i, 0 < p i) (v : Fin d → ℝ) :
--       (∑ j, ∑ k, v j * fisherMatrix p s j k * v k) = 0 ↔
--         ∀ i, directionalScore p s v i = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/EMLInformationGeometryDeepening.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/EMLInformationGeometryDeepening.lean#L70

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

theorem EMLInformationGeometryDeepening.fisher_quadForm_eq_zero_iff(p : ι → ℝ) (s : ι → Fin d → ℝ)
    (hp : ∀ i, 0 < p i) (v : Fin d → ℝ) :
    (∑ j, ∑ k, v j * fisherMatrix p s j k * v k) = 0 ↔
      ∀ i, directionalScore p s v i = 0 := by sorry
