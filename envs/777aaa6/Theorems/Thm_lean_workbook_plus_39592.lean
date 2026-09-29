-- Prove2me | Theorems.Thm_lean_workbook_plus_39592
-- name    : lean_workbook_plus_39592
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/813f4541-1d0a-4de7-be70-38dfa7ea9bc8
-- statement:
--   We know that $a^2+b^2\ge 2ab$ , therefore, either $a^2+b^2=ab$ or $a^2+b^2=2ab$ . In the first case, we have that $(a-b)^2=-ab<0$ which is impossible, hence $a^2+b^2=2ab$ , and $(a-b)^2=0\implies \boxed{a=b}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39592  (a b : ℝ)
  (h₀ : 0 ≤ a ∧ 0 ≤ b)
  (h₁ : a^2 + b^2 = a * b) :
  a = b   :=  by sorry
