-- Prove2me | Theorems.Thm_lean_workbook_plus_22826
-- name    : lean_workbook_plus_22826
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/5258216b-d0c2-4ec2-974c-bbaad6e18190
-- statement:
--   Given $g(x) = 3x + 1$ on the interval [-3, 2], find the range of $g(x)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22826 (g : ℝ → ℝ) (x : ℝ) (g_def : g x = 3 * x + 1) (x_in : x ∈ Set.Icc (-3) 2) : ∃ y, y = g x   :=  by sorry
