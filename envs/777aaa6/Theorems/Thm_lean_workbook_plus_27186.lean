-- Prove2me | Theorems.Thm_lean_workbook_plus_27186
-- name    : lean_workbook_plus_27186
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/777f9240-eaa6-40f2-b25f-dc8fc1b5b90e
-- statement:
--   To simplify the problem, assume we are traveling at a constant speed, WLOG 60 mph or 1 mile per minute. The total number of gallons of fuel used in the first 3 minutes is $x = \frac{1}{42} + \frac{1}{48} + \frac{1}{40}$ . To average 50 mpg, the number of gallons used in the 4th minute should be $\frac{4}{50} - x = \frac{29}{2800}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27186  (x : ℝ)
  (h₀ : x = 1 / 42 + 1 / 48 + 1 / 40) :
  4 / 50 - x = 29 / 2800   :=  by sorry
