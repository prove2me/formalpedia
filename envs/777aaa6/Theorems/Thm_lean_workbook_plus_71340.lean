-- Prove2me | Theorems.Thm_lean_workbook_plus_71340
-- name    : lean_workbook_plus_71340
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/d2c33d20-faa3-4b98-9b41-7ecf41431a8e
-- statement:
--   当$y=z=1$时，证明不等式$(x-1)^2x^4\geq0$成立。
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71340 (x y z : ℝ) (h₁ : y = 1) (h₂ : z = 1) : (x - 1) ^ 2 * x ^ 4 ≥ 0   :=  by sorry
