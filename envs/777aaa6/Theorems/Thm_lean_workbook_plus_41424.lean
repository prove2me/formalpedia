-- Prove2me | Theorems.Thm_lean_workbook_plus_41424
-- name    : lean_workbook_plus_41424
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/8137cfe9-d8a5-4f43-a507-a4d2d499f367
-- statement:
--   Prove that if $ab\geqq1$ ,then $a^2+b^2\geqq a+b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41424 (a b : ℝ) (hab : a * b ≥ 1) : a^2 + b^2 ≥ a + b   :=  by sorry
