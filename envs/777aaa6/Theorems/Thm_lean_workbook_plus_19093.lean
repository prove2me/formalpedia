-- Prove2me | Theorems.Thm_lean_workbook_plus_19093
-- name    : lean_workbook_plus_19093
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/6891506f-6c6e-4998-871a-c2e7dac6c3cf
-- statement:
--   $\log_63 {105}=\frac{\log_3 (3\cdot7\cdot5)}{\log_3 (3^2\cdot7)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19093 : Real.logb 6 105 = (Real.logb 3 (3*7*5)) / (Real.logb 3 (3^2*7))   :=  by sorry
