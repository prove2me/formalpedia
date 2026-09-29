-- Prove2me | Theorems.Thm_lean_workbook_plus_80943
-- name    : lean_workbook_plus_80943
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/f94d3ef6-97b4-44c4-aa12-078058a9502e
-- statement:
--   Prove that \n\n $\sin(a+b-2c) \cos b - \sin (a+c-2b) \cos c$ \n\n $= \sin (b-c) \{ \cos (b+c-a) + \cos (a+c-b) + \cos (a+b-c) \}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80943 (a b c : ℝ) :
  Real.sin (a + b - 2 * c) * Real.cos b - Real.sin (a + c - 2 * b) * Real.cos c
  = Real.sin (b - c) * (Real.cos (b + c - a) + Real.cos (a + c - b) + Real.cos (a + b - c))   :=  by sorry
