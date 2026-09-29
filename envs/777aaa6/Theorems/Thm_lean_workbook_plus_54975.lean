-- Prove2me | Theorems.Thm_lean_workbook_plus_54975
-- name    : lean_workbook_plus_54975
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/cc1f4fcf-c616-44ee-98f3-52137ba155db
-- statement:
--   Would it be $1000$ (units digit is 0) + $1000-9$ (tens digit is 0) + $1000-99$ (hundreds digit is 0) + $1000-999$ (thousands digit is 0) = $2893$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54975 1000 + (1000 - 9) + (1000 - 99) + (1000 - 999) = 2893   :=  by sorry
