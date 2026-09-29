-- Prove2me | Theorems.Thm_lean_workbook_plus_11459
-- name    : lean_workbook_plus_11459
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/ff43f940-4bb4-496e-b48e-079415b1374b
-- statement:
--   Prove that $1/2*3/4*5/6*...*99/100 < 1/12$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11459 : ∏ i in Finset.range 50, (2 * i + 1) / (2 * i + 2) < 1 / 12   :=  by sorry
