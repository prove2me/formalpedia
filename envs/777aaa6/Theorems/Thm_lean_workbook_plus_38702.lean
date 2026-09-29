-- Prove2me | Theorems.Thm_lean_workbook_plus_38702
-- name    : lean_workbook_plus_38702
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/ad1738df-f4f5-4a8b-9c63-53f00eced072
-- statement:
--   Show that $ \alpha|x| + (1 - \alpha)|y|\geq |\alpha x + (1 - \alpha)y|$ for all $ \alpha\in(0,1)$ and all real numbers $ x,y$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38702 (α : ℝ) (x y : ℝ) (hα : 0 < α ∧ α < 1) :
  α * |x| + (1 - α) * |y| ≥ |α * x + (1 - α) * y|   :=  by sorry
