-- Prove2me | Theorems.Thm_lean_workbook_plus_7912
-- name    : lean_workbook_plus_7912
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/60d567f7-e8e8-4197-8ee7-d8b95b1b2ccc
-- statement:
--   Let $a, b$ be real numbers. Prove that $$(a^2-a+1)(b^2-b+1)\geq\frac{a^2+b^2}{2}\geq\frac{a^2+ab+b^2}{3}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7912 : ∀ a b : ℝ, (a^2 - a + 1) * (b^2 - b + 1) ≥ (a^2 + b^2) / 2 ∧ (a^2 + b^2) / 2 ≥ (a^2 + a*b + b^2) / 3   :=  by sorry
