-- Prove2me | Theorems.Thm_lean_workbook_plus_7400
-- name    : lean_workbook_plus_7400
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/5751287f-9d6b-4f9d-b9b8-5b5380fde347
-- statement:
--   The smallest fraction with denominator of 99 is $\frac{50}{99}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7400 :
  IsLeast {n : ℚ | 0 < n ∧ (n.den = 99)} (50/99)   :=  by sorry
