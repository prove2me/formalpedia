-- Prove2me | Theorems.Thm_adjustment_bounded
-- name    : adjustment_bounded
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:54:42.573022+00:00
-- url     : https://prove2.me/theorems/ff467f57-4d39-4d76-8d95-ddc4a14b5315
-- title:
--   The adjustment is a weighted average, so it's bounded
-- statement:
--   The adjustment is a weighted average, so it's bounded
--
--   ```lean
--   theorem adjustment_bounded(n : ℕ) (E_Y_XZ P_Z : Fin n → ℝ)
--       (hP_nn : ∀ i, 0 ≤ P_Z i) (hP_sum : ∑ i, P_Z i = 1)
--       (lo hi : ℝ) (h_bound : ∀ i, lo ≤ E_Y_XZ i ∧ E_Y_XZ i ≤ hi) :
--       lo ≤ ∑ i, E_Y_XZ i * P_Z i ∧ ∑ i, E_Y_XZ i * P_Z i ≤ hi := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/Logic/CausalPrediction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/Logic/CausalPrediction.lean#L58

-- Thm stub generated from Speculative/Logic/CausalPrediction.lean
import Mathlib
import Definitions.Def_Speculative_Logic_CausalPrediction

/-! # CatalogBuild.MachineLearning.Prediction.CausalPrediction

Auto-generated from theorem catalog database.
Domain: MachineLearning/Prediction
Declarations: 12
-/


noncomputable section

theorem adjustment_bounded(n : ℕ) (E_Y_XZ P_Z : Fin n → ℝ)
    (hP_nn : ∀ i, 0 ≤ P_Z i) (hP_sum : ∑ i, P_Z i = 1)
    (lo hi : ℝ) (h_bound : ∀ i, lo ≤ E_Y_XZ i ∧ E_Y_XZ i ≤ hi) :
    lo ≤ ∑ i, E_Y_XZ i * P_Z i ∧ ∑ i, E_Y_XZ i * P_Z i ≤ hi := by sorry
