-- Prove2me | Theorems.Thm_lean_workbook_plus_4420
-- name    : lean_workbook_plus_4420
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/047e53d5-f2a2-4016-a9e9-dcc8aa7b8355
-- statement:
--   Show that the equation: $x^2=xsinx+cosx$ has exactly 2 solutions in $\mathbb{R}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4420 : ∃! x : ℝ, x^2 = x * Real.sin x + Real.cos x   :=  by sorry
