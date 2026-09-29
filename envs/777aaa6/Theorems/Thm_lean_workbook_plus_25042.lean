-- Prove2me | Theorems.Thm_lean_workbook_plus_25042
-- name    : lean_workbook_plus_25042
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/f9fa5271-f644-4bb8-93e8-76f0d7078e4b
-- statement:
--   So what remains is: $\log_2(\log_4 (16) ) = \log_2(2) = \boxed{1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25042 :
  Real.logb 2 (Real.logb 4 16) = 1   :=  by sorry
