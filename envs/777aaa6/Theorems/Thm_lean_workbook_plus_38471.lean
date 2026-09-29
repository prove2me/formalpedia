-- Prove2me | Theorems.Thm_lean_workbook_plus_38471
-- name    : lean_workbook_plus_38471
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/646f1210-a6a6-4a2d-922d-184b5bf3bd79
-- statement:
--   Well, $7^{6}= 117649 > 10^{5}$ , so $5 \cdot 7^{34}> 5 \cdot 7^{4}\cdot 10^{25}= 12005 \cdot 10^{25}> 1.2 \cdot 10^{29}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38471 : (5 * 7^34 : ℝ) > 1.2 * 10^29   :=  by sorry
