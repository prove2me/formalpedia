-- Prove2me | Theorems.Thm_lean_workbook_plus_66850
-- name    : lean_workbook_plus_66850
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/ec336b33-48eb-4659-8bca-1ebf331aec78
-- statement:
--   Given the proportion: \\(\\frac{A}{3} = \\frac{B}{4} = \\frac{C}{5}\\), find the values of A, B, and C.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66850 (A B C : ℝ) (h₁ : A / 3 = B / 4) (h₂ : B / 4 = C / 5) : A / 3 = C / 5 ∧ B / 4 = C / 5 ∧ A / 3 = B / 4   :=  by sorry
