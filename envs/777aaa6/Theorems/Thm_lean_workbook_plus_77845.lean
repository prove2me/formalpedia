-- Prove2me | Theorems.Thm_lean_workbook_plus_77845
-- name    : lean_workbook_plus_77845
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/634e0153-7de3-4d72-ab0e-2a1510ae2b1d
-- statement:
--   Let $P(x)=x^4+ax^3+bx^2+cx+d$ , where $a$ , $b$ , $c$ , and $d$ are constants. If $P(1)=10$ , $P(2)=20$ , and $P(3)=30$ , compute $\dfrac{P(12)+P(-8)}{10}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77845 (a b c d : ℝ) (P : ℝ → ℝ) (hP : P = fun x : ℝ => x^4 + a*x^3 + b*x^2 + c*x + d) : P 1 = 10 ∧ P 2 = 20 ∧ P 3 = 30 → (P 12 + P (-8)) / 10 = 1984   :=  by sorry
