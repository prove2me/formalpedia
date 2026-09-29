-- Prove2me | Theorems.Thm_lean_workbook_plus_72417
-- name    : lean_workbook_plus_72417
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/381c6b0e-8ef5-42e8-a89a-766cb0a31e75
-- statement:
--   Prove that $ \cos(2\pi/7)+\cos(4\pi/7)+\cos(6\pi/7) = -(cos(\frac{\pi}{7})+cos(\frac{3 \pi}{7})+cos(\frac{5 \pi}{7}))$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72417 :  Real.cos (2 * π / 7) + Real.cos (4 * π / 7) + Real.cos (6 * π / 7) = - (Real.cos (π / 7) + Real.cos (3 * π / 7) + Real.cos (5 * π / 7))   :=  by sorry
