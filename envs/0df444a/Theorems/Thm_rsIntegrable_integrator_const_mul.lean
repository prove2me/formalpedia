-- Prove2me | Theorems.Thm_rsIntegrable_integrator_const_mul
-- name    : rsIntegrable_integrator_const_mul
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:48:42.539747+00:00
-- url     : https://prove2.me/theorems/b6fb6b1b-57ff-4ae8-8861-b9194f8b3aeb
-- title:
--   Source theorem: rsIntegrable_integrator_const_mul
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
end Theorem_1_3
section integrator_scalar_multiply

theorem rsIntegrable_integrator_const_mul {f α : ℝ → ℝ} {a b k : ℝ}
    (hk : 0 ≤ k) (h : RSIntegrable f α a b) :
    RSIntegrable f (fun x => k * α x) a b := by
  sorry
end integrator_scalar_multiply
end
