-- Prove2me | Theorems.Thm_lean_workbook_plus_14480
-- name    : lean_workbook_plus_14480
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/d0c1e925-919f-4e19-ad1e-f4d73db22d3f
-- statement:
--   Let Derek's rate be a, Mark's rate be b, and Alex's rate be c. Note that $\frac{1}{b}$ + $\frac{1}{c}$ = $\frac{1}{9}$ $\frac{1}{a}$ + $\frac{1}{c}$ = $\frac{1}{10}$ $\frac{1}{a}$ + $\frac{1}{b}$ = $\frac{1}{11}$ Adding all these up and dividing by two, we get $\frac{1}{a}$ + $\frac{1}{b}$ + $\frac{1}{c}$ = $\frac{299}{1980}$ . And thus, we get that the answer is the reciprocal of that, which is $\frac{1980}{299}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14480  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : 1 / b + 1 / c = 1 / 9)
  (h₂ : 1 / a + 1 / c = 1 / 10)
  (h₃ : 1 / a + 1 / b = 1 / 11) :
  1 / a + 1 / b + 1 / c = 299 / 1980   :=  by sorry
