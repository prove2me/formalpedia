-- Prove2me | Theorems.Thm_lean_workbook_plus_6699
-- name    : lean_workbook_plus_6699
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/ee2124cc-1d3d-4243-a5e5-79855d70b0cc
-- statement:
--   $=9-3\left(\cos^2a+\cos^2b+\cos^2c\right)\leq9-\left(\cos a+\cos b+\cos c\right)^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6699 (a b c : ℝ) :
  9 - 3 * (Real.cos a ^ 2 + Real.cos b ^ 2 + Real.cos c ^ 2) ≤ 9 - (Real.cos a + Real.cos b + Real.cos c) ^ 2   :=  by sorry
