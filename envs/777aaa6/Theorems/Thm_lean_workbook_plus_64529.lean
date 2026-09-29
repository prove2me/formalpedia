-- Prove2me | Theorems.Thm_lean_workbook_plus_64529
-- name    : lean_workbook_plus_64529
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/c6ea3ee5-8027-47b3-89ba-ca0ba8b3f185
-- statement:
--   Prove that $(A^2 + B^2 + C^2)^2 - 2(A^4 + B^4 + C^4) = (A+B+C)(A+B-C)(B+C-A)(C+A-B)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64529 (A B C : ℝ) : (A^2 + B^2 + C^2)^2 - 2 * (A^4 + B^4 + C^4) = (A + B + C) * (A + B - C) * (B + C - A) * (C + A - B)   :=  by sorry
