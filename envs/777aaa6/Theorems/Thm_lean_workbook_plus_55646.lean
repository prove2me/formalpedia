-- Prove2me | Theorems.Thm_lean_workbook_plus_55646
-- name    : lean_workbook_plus_55646
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/e62142d1-31e0-4f77-a636-d5f76dbcb5a2
-- statement:
--   $$\frac{1}{x^2}+\frac{4}{y^2}\ge 2\left(\frac{1}{x}+\frac{1}{y} \right)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55646 : ∀ x y : ℝ, (x ≠ 0 ∧ y ≠ 0) → 1 / x ^ 2 + 4 / y ^ 2 ≥ 2 * (1 / x + 1 / y)   :=  by sorry
