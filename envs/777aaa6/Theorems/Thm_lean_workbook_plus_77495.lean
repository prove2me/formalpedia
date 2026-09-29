-- Prove2me | Theorems.Thm_lean_workbook_plus_77495
-- name    : lean_workbook_plus_77495
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/45a8355c-0cc0-41de-b853-26cf18b3c023
-- statement:
--   For $ k>0$ and $ 0\leq a, b, c, d\leq k,$ prove that the following inequality holds \n\n $ 2k^2-k(a+b+c+d)+ab+bc+cd+da\geq0$ \n\n When does equality hold ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77495 (k a b c d : ℝ) (h₁ : 0 < k) (h₂ : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d) (h₃ : a ≤ k ∧ b ≤ k ∧ c ≤ k ∧ d ≤ k) : 2 * k ^ 2 - k * (a + b + c + d) + a * b + b * c + c * d + d * a ≥ 0   :=  by sorry
