-- Prove2me | Theorems.Thm_lean_workbook_plus_38063
-- name    : lean_workbook_plus_38063
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/fb9a7244-ee59-4a14-891b-ebb3a0e624f0
-- statement:
--   it's $ 3a^{2}-12a\leq0 ,0\leq a\leq4 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38063 (a : ℝ) (h₁ : 3 * a ^ 2 - 12 * a ≤ 0) (h₂ : 0 ≤ a) (h₃ : a ≤ 4) : 0 ≤ a ∧ a ≤ 4   :=  by sorry
