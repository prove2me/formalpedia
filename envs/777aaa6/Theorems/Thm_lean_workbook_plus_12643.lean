-- Prove2me | Theorems.Thm_lean_workbook_plus_12643
-- name    : lean_workbook_plus_12643
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/016914e4-c5e9-4fcd-884c-909fd6004fb6
-- statement:
--   Show that there are infinitely many integer solutions $ (m,n) $ for the equation $(m+1)(n-1) = (m-n+1)(m-n-1).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12643 (m n : ℤ) : ∃ m n, (m+1)*(n-1) = (m-n+1)*(m-n-1)   :=  by sorry
