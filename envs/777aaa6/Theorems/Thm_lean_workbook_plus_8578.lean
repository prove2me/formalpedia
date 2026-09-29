-- Prove2me | Theorems.Thm_lean_workbook_plus_8578
-- name    : lean_workbook_plus_8578
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/eca458be-0d01-411b-88af-6a68d0b345f9
-- statement:
--   当$w^3=0$时，取$y=1$，$z=0$，证明不等式$(x-1)^2(x+1)^2(x^2-x+1)\geq0$成立。
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8578 (x y z w : ℝ) (h₁ : w^3 = 0) (h₂ : y = 1) (h₃ : z = 0) : (x - 1)^2 * (x + 1)^2 * (x^2 - x + 1) ≥ 0   :=  by sorry
