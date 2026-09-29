-- Prove2me | Theorems.Thm_lean_workbook_plus_75246
-- name    : lean_workbook_plus_75246
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/92d528ca-01d4-44da-823d-ab5ac73b0e4e
-- statement:
--   Explain why $|y| > |2y^2|$ when $-\frac{1}{2} < y < 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75246 (y : ℝ) (hy : -1 / 2 < y ∧ y < 0) : |y| > |2*y^2|   :=  by sorry
