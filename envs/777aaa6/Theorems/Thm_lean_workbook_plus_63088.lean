-- Prove2me | Theorems.Thm_lean_workbook_plus_63088
-- name    : lean_workbook_plus_63088
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/20e944cb-7215-43c7-af9a-750e92fdc3b8
-- statement:
--   Find the equation of the line $g(x)$ that joins the points $(k, f(k))$ and $(k+1, f(k+1))$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63088 (f : ℝ → ℝ) (k : ℝ) : ∃ g : ℝ → ℝ, g x = f k + (f (k + 1) - f k) * (x - k)   :=  by sorry
