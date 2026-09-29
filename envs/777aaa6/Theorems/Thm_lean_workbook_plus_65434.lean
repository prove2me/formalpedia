-- Prove2me | Theorems.Thm_lean_workbook_plus_65434
-- name    : lean_workbook_plus_65434
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/bed4f554-83da-4db1-ac4d-647588c73f86
-- statement:
--   From the first two equations results, by subtraction, $d=\dfrac{3}{2}$ . \nResults the system of equations (symmetrical in $a,b,c$ ): \n $\begin{cases} a+b+c=\dfrac{5}{2}\a^2+b^2+c^2=\dfrac{25}{12}\abc=\dfrac{125}{216}.\end{cases}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65434 (a b c d : ℝ) (h₁ : a + b + c + d = 5 / 2) (h₂ : a^2 + b^2 + c^2 + d^2 = 25 / 12) (h₃ : a * b * c * d = 125 / 216) : a * b * c * d = 125 / 216 ∧ a + b + c + d = 5 / 2 ∧ a^2 + b^2 + c^2 + d^2 = 25 / 12   :=  by sorry
