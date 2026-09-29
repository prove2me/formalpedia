-- Prove2me | Theorems.Thm_lean_workbook_plus_36909
-- name    : lean_workbook_plus_36909
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/f6d23aa8-aab4-4250-99d3-a85feda24f64
-- statement:
--   we know that $\\cos\\frac{a}{2}\\ge-1$ (1) and $\\cos\\frac{b}{2}\\ge -1$ (2)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36909 : ∀ a b : ℝ, Real.cos (a / 2) ≥ -1 ∧ Real.cos (b / 2) ≥ -1   :=  by sorry
