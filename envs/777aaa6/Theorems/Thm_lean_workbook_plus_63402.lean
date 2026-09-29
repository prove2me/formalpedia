-- Prove2me | Theorems.Thm_lean_workbook_plus_63402
-- name    : lean_workbook_plus_63402
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/1f4dd8ee-a7fa-40b1-bd0d-848e83277edc
-- statement:
--   1) AM-HM \n \n $\frac{a+b+c}{3}\geq\frac{3}{\frac{1}{a}+\frac{1}{b}+\frac{1}{c}}$ \n \n So, \n $9+ \left( a+b+c\right) \left( \frac{1}{a}+\frac{1}{b}+\frac{1}{c}\right) \geq 6\cdot 3$ ....(1)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63402 : ∀ a b c : ℝ, 9 + (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 6 * 3   :=  by sorry
