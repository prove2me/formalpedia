-- Prove2me | Theorems.Thm_lean_workbook_plus_11950
-- name    : lean_workbook_plus_11950
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/f5d86adc-75b9-4f41-9498-9bcfb0e60a62
-- statement:
--   Prove: $ cos3x = cosx( 1 - 4sin^2x)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11950 x : Real.cos (3 * x) = Real.cos x * (1 - 4 * (Real.sin x)^2)   :=  by sorry
