-- Prove2me | Theorems.Thm_lean_workbook_plus_15898
-- name    : lean_workbook_plus_15898
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/61e7434b-f3cd-4a04-8453-1dfd8d79737b
-- statement:
--   this is a trigonometric ineq which equivalent to : $ -1 \le Cos \ \alpha \le 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15898 (α : ℝ) : -1 ≤ Real.cos α ∧ Real.cos α ≤ 1   :=  by sorry
