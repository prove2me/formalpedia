-- Prove2me | Theorems.Thm_lean_workbook_plus_21497
-- name    : lean_workbook_plus_21497
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/0fd85aa3-1573-49f7-a773-f42927959fe8
-- statement:
--   Show that the expression $(a - b)^2(c - d)^2+(ad - bc)^2$ is always non-negative.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21497 (a b c d : ℝ) : (a - b) ^ 2 * (c - d) ^ 2 + (a * d - b * c) ^ 2 ≥ 0   :=  by sorry
