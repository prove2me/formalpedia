-- Prove2me | Theorems.Thm_lean_workbook_plus_2601
-- name    : lean_workbook_plus_2601
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/2a3c7e5e-9a4b-4b87-ac4c-139bb9544c53
-- statement:
--   Given $x=y=z=0$, does the statement hold?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2601 : x = y ∧ y = z ∧ z = 0 → x = 0 ∧ y = 0 ∧ z = 0   :=  by sorry
