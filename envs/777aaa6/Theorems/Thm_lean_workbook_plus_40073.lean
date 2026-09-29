-- Prove2me | Theorems.Thm_lean_workbook_plus_40073
-- name    : lean_workbook_plus_40073
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/a51fb714-1926-4e49-976d-6bb51fdbe367
-- statement:
--   $\\left(x - \\frac{i}{2} \right)^5 = \\left( x + \\frac{i}{2} \right)^5$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40073 : ∀ x : ℝ, (x - (1 / 2 * Complex.I))^5 = (x + (1 / 2 * Complex.I))^5   :=  by sorry
