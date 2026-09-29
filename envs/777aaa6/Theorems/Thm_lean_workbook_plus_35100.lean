-- Prove2me | Theorems.Thm_lean_workbook_plus_35100
-- name    : lean_workbook_plus_35100
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/2582bfc3-2a0c-4fe6-a21c-c3b2c0b489b6
-- statement:
--   Prove the equation: $\mathbf{A}( 2\mathbf{w} - 3\mathbf{v}) = 2(\mathbf{Aw}) - 3(\mathbf{Av}).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35100 (w v : ℝ) : A * (2 * w - 3 * v) = 2 * (A * w) - 3 * (A * v)   :=  by sorry
