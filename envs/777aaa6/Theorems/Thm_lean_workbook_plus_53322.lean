-- Prove2me | Theorems.Thm_lean_workbook_plus_53322
-- name    : lean_workbook_plus_53322
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/3db0bc36-2461-4ea6-ac22-b9b98dde827f
-- statement:
--   Is the inequality\n\n \( (a+b+c-1)^2-1\geq\frac{3}{8}\cdot(a+b)(b+c)(c+a) \)\ntrue, or not?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53322 : ∀ a b c : ℝ, (a + b + c - 1) ^ 2 - 1 ≥ (3 / 8 : ℝ) * (a + b) * (b + c) * (c + a)   :=  by sorry
