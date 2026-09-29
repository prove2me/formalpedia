-- Prove2me | Theorems.Thm_lean_workbook_plus_31896
-- name    : lean_workbook_plus_31896
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/61b02678-58f4-45f5-b4ca-64a3543b1298
-- statement:
--   After the hint, the equation becomes\n $-7\, \left( \tan \left( x \right) \right) ^{6}+35\, \left( \tan \left( x \right) \right) ^{4}-21\, \left( \tan \left( x \right) \right) ^{2}+1=0$ .\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31896 :
  ∀ x : ℝ, (x ≠ π / 2 ∧ x ≠ -π / 2) → -7 * (tan x)^6 + 35 * (tan x)^4 - 21 * (tan x)^2 + 1 = 0   :=  by sorry
