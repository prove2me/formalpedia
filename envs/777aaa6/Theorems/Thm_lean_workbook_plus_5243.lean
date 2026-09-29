-- Prove2me | Theorems.Thm_lean_workbook_plus_5243
-- name    : lean_workbook_plus_5243
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/dd0b9129-877c-4a3e-852d-1b5b83c333c2
-- statement:
--   Prove that $ \frac {1*3*5*7*...*9997*9999}{2*4*6*8*...*9998*10000} < 1/100.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5243 : (∏ i in Finset.range 5000, (2 * i + 1)) / (∏ i in Finset.range 5000, (2 * i + 2)) < 1 / 100   :=  by sorry
