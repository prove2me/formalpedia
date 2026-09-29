-- Prove2me | Theorems.Thm_lean_workbook_plus_62752
-- name    : lean_workbook_plus_62752
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/0613a2b9-cf0b-4e64-a21e-4a8451d01987
-- statement:
--   Express the single sum in terms of the Euler-Mascheroni constant \(\gamma\) and the logarithm of a product: \(\frac12 \gamma + \ln\left(\left(\frac12\right) !\right) - \frac12 + \ln \frac32\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62752 (h₁ : 0 < (2 : ℝ)) : 1 / 2 * γ + Real.log ((1 / 2)! * 3 / 2) - 1 / 2 = 1 / 2 * γ + Real.log ((1 / 2)! * 3 / 2) - 1 / 2   :=  by sorry
