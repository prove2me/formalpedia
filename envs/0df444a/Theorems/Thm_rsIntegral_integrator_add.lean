-- Prove2me | Theorems.Thm_rsIntegral_integrator_add
-- name    : rsIntegral_integrator_add
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:48:19.299317+00:00
-- url     : https://prove2.me/theorems/18d14a51-2dfb-4ace-9f5d-c50eeb4548ff
-- title:
--   Source theorem: rsIntegral_integrator_add
-- statement:
--   Source theorem extracted from ProbabilityTheory.chapter_01.thm_1_3, with its proposition and original proof recorded separately.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_3.lean

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_3_F001
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic
open scoped BigOperators Pointwise
open Finset
open Set
noncomputable section
section Thm_1_3_helper
end Thm_1_3_helper
section Theorem_1_3

theorem rsIntegral_integrator_add {f α₁ α₂ : ℝ → ℝ} {a b : ℝ}
    (h₁ : RSIntegrable f α₁ a b)
    (h₂ : RSIntegrable f α₂ a b) :
  rsIntegral f (fun x => α₁ x + α₂ x) a b (rsIntegrable_integrator_add h₁ h₂) =
    rsIntegral f α₁ a b h₁ + rsIntegral f α₂ a b h₂ := by
  sorry
end Theorem_1_3
end
