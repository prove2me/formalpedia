-- Prove2me | Theorems.Thm_lean_workbook_plus_4183
-- name    : lean_workbook_plus_4183
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/25693f4e-2966-4c3e-abe3-c878a5a15244
-- statement:
--   $\log_6 2+\log_6 3=\log_6 (2\cdot 3)=\log_6 6=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4183 :
  Real.log 2 / Real.log 6 + Real.log 3 / Real.log 6 = 1   :=  by sorry
