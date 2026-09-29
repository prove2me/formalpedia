-- Prove2me | Theorems.Thm_lean_workbook_plus_40212
-- name    : lean_workbook_plus_40212
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/36b053bf-e9e4-44fb-bc25-d92717ea5383
-- statement:
--   for all $n>0$ prove that \n $n^{21}+n^{16}-2n^{6}+1>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40212 (n : ℕ) (hn : n > 0) : n ^ 21 + n ^ 16 - 2 * n ^ 6 + 1 > 0   :=  by sorry
