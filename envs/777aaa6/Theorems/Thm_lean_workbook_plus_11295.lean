-- Prove2me | Theorems.Thm_lean_workbook_plus_11295
-- name    : lean_workbook_plus_11295
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/3e9b173c-b796-41a7-8d85-b0ca0172fb59
-- statement:
--   RHS $=2^{-\sqrt2}=(4^{\frac{1}{2}})^{-\sqrt2}=4^{-\frac{\sqrt{2}}{2}}=(4^{-1})^{\frac{\sqrt{2}}{2}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11295 :
  (2 : ℝ)^(-Real.sqrt 2) = ((4 : ℝ)^(1 / 2))^(-Real.sqrt 2)   :=  by sorry
