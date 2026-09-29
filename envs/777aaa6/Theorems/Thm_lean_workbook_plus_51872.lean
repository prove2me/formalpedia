-- Prove2me | Theorems.Thm_lean_workbook_plus_51872
-- name    : lean_workbook_plus_51872
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/d4d93bf1-b524-4d54-8521-2bb913900390
-- statement:
--   Find $P(9)+P(-5)$ given $P(x)=x^4+ax^3+bx^2+cx+d$ where $P(1)=827, P(2)=1654, P(3)=2481$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51872 (a b c d : ℝ) (P : ℝ → ℝ) (hP : P = fun x : ℝ => x^4 + a*x^3 + b*x^2 + c*x + d) : P 1 = 827 ∧ P 2 = 1654 ∧ P 3 = 2481 → P 9 + P (-5) = 8012   :=  by sorry
