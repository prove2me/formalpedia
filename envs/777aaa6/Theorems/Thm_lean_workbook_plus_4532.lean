-- Prove2me | Theorems.Thm_lean_workbook_plus_4532
-- name    : lean_workbook_plus_4532
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/2c1b5b31-746b-4cff-b3d6-b6604ed6bc1e
-- statement:
--   Let $p(x)$ be defined as $x^4+ax^3+bx^2+cx+d=0$ where $a,b,c,d$ are constants. If $p(1)=10, p(2)=20, p(3)=30$ , then find $\frac{p(12)+p(-8)}{10}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4532 (a b c d : ℝ) (p : ℝ → ℝ) (h₁ : p = fun x => x^4 + a*x^3 + b*x^2 + c*x + d) : p 1 = 10 ∧ p 2 = 20 ∧ p 3 = 30 → (p 12 + p (-8)) / 10 = 1984   :=  by sorry
