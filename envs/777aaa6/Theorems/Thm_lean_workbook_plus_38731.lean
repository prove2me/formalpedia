-- Prove2me | Theorems.Thm_lean_workbook_plus_38731
-- name    : lean_workbook_plus_38731
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/12b599ca-cd05-43f4-bbda-76e071ccb87a
-- statement:
--   5) $ 1 <\frac{1}{n+1}+\frac{1}{n+2}+....+\frac{1}{3n+1}< 2 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38731 : ∀ n : ℕ, 1 < ∑ k in Finset.Icc (n + 1) (3 * n + 1), (1 : ℝ) / k ∧ ∑ k in Finset.Icc (n + 1) (3 * n + 1), (1 : ℝ) / k < 2   :=  by sorry
