-- Prove2me | Theorems.Thm_lean_workbook_plus_52924
-- name    : lean_workbook_plus_52924
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/46abb564-66c5-4aac-b94b-4d12bd612b48
-- statement:
--   If $a-b=1$ ,\n $a^2-b^2=(a-b)(a+b)=a+b$ \n $\therefore n^2-(n-1)^2=2n-1$ $\rightarrow$ Difference between two consecutive squares
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52924  (n : ℕ) :
  n^2 - (n - 1)^2 = 2 * n - 1   :=  by sorry
