-- Prove2me | Theorems.Thm_lean_workbook_plus_63251
-- name    : lean_workbook_plus_63251
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/2794fb65-73b5-4eae-bab2-77c928fbb1c6
-- statement:
--   Identify the largest value among the fractions $\frac{3}{7}$, $\frac{4}{9}$, $\frac{17}{35}$, $\frac{100}{201}$, and $\frac{151}{301}$ without actually calculating their exact values.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63251 : (3 : ℚ) / 7 < 4 / 9 ∧ (4 : ℚ) / 9 < 17 / 35 ∧ (17 : ℚ) / 35 < 100 / 201 ∧ (100 : ℚ) / 201 < 151 / 301   :=  by sorry
