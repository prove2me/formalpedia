-- Prove2me | Theorems.Thm_lean_workbook_plus_61096
-- name    : lean_workbook_plus_61096
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/53e28cd9-c9e3-4a79-81d3-1b1904eef122
-- statement:
--   $ a=-1$ and $ b=-2$ and the solution $ \boxed{f(x)=-x-2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61096 (a b : ℝ) (f : ℝ → ℝ) (hf: f = fun x => a * x + b) : a = -1 ∧ b = -2 → f = fun x => -x - 2   :=  by sorry
