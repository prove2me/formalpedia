-- Prove2me | Theorems.Thm_lean_workbook_plus_13249
-- name    : lean_workbook_plus_13249
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/ab2579a0-972c-4dcf-a91f-e79698384c26
-- statement:
--   If $2x-\frac{1}{3x}=2$ find the value of $3x-\frac{1}{2x}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13249 (x : ℝ) (hx : 2*x - 1/(3*x) = 2) : 3*x - 1/(2*x) = 3   :=  by sorry
