-- Prove2me | Theorems.Thm_lean_workbook_plus_27520
-- name    : lean_workbook_plus_27520
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/718537aa-1d88-48ee-95fc-2a415706697c
-- statement:
--   Prove that \(\cos(3x) - \cos(5x) = 2\sin(x) \sin(4x)\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27520 (x : ℝ) :
  Real.cos (3 * x) - Real.cos (5 * x) = 2 * Real.sin x * Real.sin (4 * x)   :=  by sorry
