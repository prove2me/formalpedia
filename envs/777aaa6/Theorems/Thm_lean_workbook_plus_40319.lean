-- Prove2me | Theorems.Thm_lean_workbook_plus_40319
-- name    : lean_workbook_plus_40319
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/adf6ef34-9384-4b78-8ab7-e7fff8bf617c
-- statement:
--   $$\frac{1}{x^2}+\frac{2}{y^2}\ge \sqrt 2\left(\frac{1}{x}+\frac{1}{y} \right)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40319 : ∀ x y : ℝ, (x ≠ 0 ∧ y ≠ 0) → 1 / x ^ 2 + 2 / y ^ 2 ≥ Real.sqrt 2 * (1 / x + 1 / y)   :=  by sorry
