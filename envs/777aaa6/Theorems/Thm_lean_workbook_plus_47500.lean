-- Prove2me | Theorems.Thm_lean_workbook_plus_47500
-- name    : lean_workbook_plus_47500
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/68f4b9ba-23a7-46d2-8072-f804b0fc5ce0
-- statement:
--   for all $n>0$ prove that \n $n^{21}+n^{16}-2n^{6}+1>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47500 (n : ℕ) (hn : 0 < n) : n^21 + n^16 - 2*n^6 + 1 > 0   :=  by sorry
