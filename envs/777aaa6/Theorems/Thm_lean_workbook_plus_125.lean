-- Prove2me | Theorems.Thm_lean_workbook_plus_125
-- name    : lean_workbook_plus_125
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/c8253121-361c-4d99-8c3c-dd2bb077de5b
-- statement:
--   If the polynom $ ax^{3} + bx^{2} + cx + d$ is divisble by 5 for all x prove that $ 5|a,b,c,d$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_125 (a b c d : ℤ) (h : ∀ x, 5 ∣ a * x ^ 3 + b * x ^ 2 + c * x + d) : 5 ∣ a ∧ 5 ∣ b ∧ 5 ∣ c ∧ 5 ∣ d   :=  by sorry
