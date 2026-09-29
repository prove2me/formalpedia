-- Prove2me | Theorems.Thm_lean_workbook_plus_17200
-- name    : lean_workbook_plus_17200
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/e4dd2751-72a4-4872-9b8b-bf6926968173
-- statement:
--   $q(-1)=3+4a-6-12a+b=b-3-8a$, $q(a)=3a^4-4a^4-6a^2+12a^2+b=b-a^4+6a^2$, $q(1)=3-4a-6+12a+b=b-3+8a$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17200 (a : ℝ) (q : ℝ → ℝ) (h₀ : q (-1) = 3 + 4 * a - 6 - 12 * a + b) (h₁ : q a = 3 * a ^ 4 - 4 * a ^ 4 - 6 * a ^ 2 + 12 * a ^ 2 + b) (h₂ : q 1 = 3 - 4 * a - 6 + 12 * a + b) : q (-1) = b - 3 - 8 * a ∧ q a = b - a ^ 4 + 6 * a ^ 2 ∧ q 1 = b - 3 + 8 * a   :=  by sorry
