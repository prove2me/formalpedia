-- Prove2me | Theorems.Thm_lean_workbook_plus_60775
-- name    : lean_workbook_plus_60775
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/592dac7a-9c05-4b2d-a1c2-d6f703c8fb49
-- statement:
--   For all $\\alpha \\in (0, \\frac{\\pi}{4})$ , we have:\n\n $\\sin \\alpha < \\cos \\alpha$\n\n $\\sin \\alpha < \\tan \\alpha$\n\n $\\tan \\alpha < \\cot \\alpha$\n\n $\\cos \\alpha < \\cot \\alpha$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60775 (α : ℝ) (hα : 0 < α ∧ α < Real.pi / 4) : Real.sin α < Real.cos α   :=  by sorry
