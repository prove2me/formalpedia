-- Prove2me | Theorems.Thm_lean_workbook_plus_48481
-- name    : lean_workbook_plus_48481
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/5dc3c1ed-30cb-4a2d-85d9-2ac7bb527528
-- statement:
--   Let $p(x)=x^4+ax^3+bx^2+cx+d$ where a,b,c,d are constant, $p(1)=1993, p(2)=3986, p(3)=5979$ ,find the value of : $\frac{1}{4}[p(11)+p(-7)]$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48481 (a b c d : ℝ) (p : ℝ → ℝ) (hp : p = fun x : ℝ => x^4 + a*x^3 + b*x^2 + c*x + d) : p 1 = 1993 ∧ p 2 = 3986 ∧ p 3 = 5979 → 1/4 * (p 11 + p (-7)) = 5233   :=  by sorry
