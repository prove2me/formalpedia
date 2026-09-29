-- Prove2me | Theorems.Thm_lean_workbook_plus_162
-- name    : lean_workbook_plus_162
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/4517984b-eb73-4f67-a1df-a9ab9509f558
-- statement:
--   Prove that \n\n $\cos(a+b) \sin b - \cos (a+c) \sin c = \sin(a+b) \cos b - \sin (a+c) \cos c$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_162  (a b c : ℝ) :
  Real.cos (a + b) * Real.sin b - Real.cos (a + c) * Real.sin c
    = Real.sin (a + b) * Real.cos b - Real.sin (a + c) * Real.cos c   :=  by sorry
