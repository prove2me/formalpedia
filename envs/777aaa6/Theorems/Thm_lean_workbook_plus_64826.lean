-- Prove2me | Theorems.Thm_lean_workbook_plus_64826
-- name    : lean_workbook_plus_64826
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/ebbc1e2f-d2ea-4b9d-b0ab-e0426d6ba8ff
-- statement:
--   When $ ( x + y ) = ( y + z ) = ( z + x ) = 0 $ . Then we have, $ x = y = z = 0 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64826 (x y z : ℝ) (h : x + y = 0 ∧ y + z = 0 ∧ z + x = 0) : x = 0 ∧ y = 0 ∧ z = 0   :=  by sorry
