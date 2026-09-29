-- Prove2me | Theorems.Thm_lean_workbook_plus_14666
-- name    : lean_workbook_plus_14666
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/3f7104b4-b5dd-458a-be89-839c381bf092
-- statement:
--   We wish to show that $abc(a^2+b^2+c^2) \leq \frac{(a+b+c)^5}{81}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14666 : ∀ a b c : ℝ, a * b * c * (a ^ 2 + b ^ 2 + c ^ 2) ≤ (a + b + c) ^ 5 / 81   :=  by sorry
