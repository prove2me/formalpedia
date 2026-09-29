-- Prove2me | Theorems.Thm_lean_workbook_plus_5537
-- name    : lean_workbook_plus_5537
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/a9e3f7c5-4af1-4b60-b56a-a0c24d803754
-- statement:
--   Thus $y\neq 0\implies 7-(x-y)^2=2(x-y)-8\iff (x-y)^2+2(x-y)-15=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5537 (x y : ℝ) (h₁ : y ≠ 0) (h₂ : 7 - (x - y) ^ 2 = 2 * (x - y) - 8) : (x - y) ^ 2 + 2 * (x - y) - 15 = 0   :=  by sorry
