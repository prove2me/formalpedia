-- Prove2me | Theorems.Thm_lean_workbook_plus_15094
-- name    : lean_workbook_plus_15094
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/6f56a4ea-c518-4446-8804-e0b47391c409
-- statement:
--   $\frac{1}{x^{2}+4}\geq\frac{4-x}{16}\iff x(x-2)^{2}\geq\ 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15094 : ∀ x : ℝ, (x ^ 2 + 4 ≠ 0 ∧ 16 ≠ 0) →
  (1 / (x ^ 2 + 4) ≥ (4 - x) / 16 ↔ x * (x - 2) ^ 2 ≥ 0)   :=  by sorry
