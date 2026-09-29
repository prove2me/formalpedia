-- Prove2me | Theorems.Thm_lean_workbook_plus_7077
-- name    : lean_workbook_plus_7077
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/d49a4298-b8e6-4ee0-9e14-8919c5480fbf
-- statement:
--   Graph the curve given by $x=4t-\sin(t) , y=4-\cos(t)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7077 (x y t : ℝ) (h₁ : x = 4 * t - Real.sin t) (h₂ : y = 4 - Real.cos t) : x^2 + y^2 = (4 * t - Real.sin t)^2 + (4 - Real.cos t)^2   :=  by sorry
