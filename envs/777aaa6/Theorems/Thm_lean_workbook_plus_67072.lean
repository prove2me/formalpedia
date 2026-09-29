-- Prove2me | Theorems.Thm_lean_workbook_plus_67072
-- name    : lean_workbook_plus_67072
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/4d4b6d24-34ef-41cf-9ba6-d5779acbba58
-- statement:
--   Here is my original example: \n\n $f(x)=\begin{cases} 0, & \text{if}\ x < -1-\frac{b}{a}\\ \frac{a}{a-b} x + \frac{2a}{a-b}, & \text{if}\ -1-\frac{b}{a} \leq x \leq -2\\ 1, & \text{if}\ -2 < x\\ \end{cases}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67072  (a b : ℝ)
  (f : ℝ → ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : a ≠ b)
  (h₂ : ∀ x < -1 - b / a, f x = 0)
  (h₃ : ∀ x, -1 - b / a ≤ x ∧ x ≤ -2 → f x = a / (a - b) * x + 2 * a / (a - b))
  (h₄ : ∀ x > -2, f x = 1) :
  ∀ x, f x = if x < -1 - b / a then 0 else if -1 - b / a ≤ x ∧ x ≤ -2 then a / (a - b) * x + 2 * a / (a - b) else 1   :=  by sorry
