-- Prove2me | Theorems.Thm_lean_workbook_plus_51295
-- name    : lean_workbook_plus_51295
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/044642ae-03e3-4f3d-9a49-38ecaf4a4583
-- statement:
--   Let $\Delta ABC$ show that \n $1+cosAcosBcosC \ge \sqrt3sinAsinBsinC$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51295 : ∀ A B C : ℝ, 1 + Real.cos A * Real.cos B * Real.cos C ≥ Real.sqrt 3 * Real.sin A * Real.sin B * Real.sin C   :=  by sorry
