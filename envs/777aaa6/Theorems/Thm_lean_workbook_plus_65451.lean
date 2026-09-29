-- Prove2me | Theorems.Thm_lean_workbook_plus_65451
-- name    : lean_workbook_plus_65451
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/6cdfb737-b745-41bc-9c43-4d3ec7c594df
-- statement:
--   Derive the identity $\frac{\sin 3x}{\sin x} = 2\cos 2x + 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65451 : ∀ x : ℝ, sin 3*x / sin x = 2 * cos 2*x + 1   :=  by sorry
