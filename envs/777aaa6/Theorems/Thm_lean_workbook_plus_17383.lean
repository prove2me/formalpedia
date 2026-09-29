-- Prove2me | Theorems.Thm_lean_workbook_plus_17383
-- name    : lean_workbook_plus_17383
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/84397504-5888-431f-b75b-08e79a1a8726
-- statement:
--   Simplify $\frac{(i-1)^5}{5}+\frac{(i-1)^4}{2}+\frac{(i-1)^3}{3}-\frac{i}{30}+\frac{1}{30}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17383 (i : ℂ) : (i - 1) ^ 5 / 5 + (i - 1) ^ 4 / 2 + (i - 1) ^ 3 / 3 - i / 30 + 1 / 30 = i ^ 5 / 5 - i ^ 4 / 2 + i ^ 3 / 3 - i / 30   :=  by sorry
