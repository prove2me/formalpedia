-- Prove2me | Theorems.Thm_lean_workbook_plus_29115
-- name    : lean_workbook_plus_29115
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/fa9d37a3-de05-4332-bd6f-945fc5addc38
-- statement:
--   What are your thoughts about? $$f(x) = \begin{cases} x & [0, 1] \ x - 2 & (1, 2] \end{cases}$$ and $$g(x) = \begin{cases} -x & [0, 1] \ -x + 2 & (1, 2] \end{cases}$$ Thus, $$f(x) + g(x) = \begin{cases} 0 & [0, 1] \ 0 & (1, 2] \end{cases}$$ As a result, the sum has a limit.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29115  (f g : ℝ → ℝ)
  (h₀ : ∀ x, 0 ≤ x ∧ x ≤ 1 → f x = x)
  (h₁ : ∀ x, 1 < x ∧ x ≤ 2 → f x = x - 2)
  (h₂ : ∀ x, 0 ≤ x ∧ x ≤ 1 → g x = -x)
  (h₃ : ∀ x, 1 < x ∧ x ≤ 2 → g x = -x + 2) :
  ∀ x, 0 ≤ x ∧ x ≤ 2 → f x + g x = 0   :=  by sorry
