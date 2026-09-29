-- Prove2me | Theorems.Thm_lean_workbook_plus_58123
-- name    : lean_workbook_plus_58123
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/8a726f14-6b79-4a33-ab2b-aaba15645d52
-- statement:
--   Let $a>0$ and $x_1,x_2,x_3$ be real numbers with $x_1+x_2+x_3=0$ . Prove that \n $$\log_2\left(1+a^{x_1}\right)+\log_2\left(1+a^{x_2}\right)+\log_2\left(1+a^{x_3}\right)\ge3.$$\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58123 (a : ℝ) (hx: x1 + x2 + x3 = 0) : Real.logb 2 (1 + a^x1) + Real.logb 2 (1 + a^x2) + Real.logb 2 (1 + a^x3) ≥ 3   :=  by sorry
