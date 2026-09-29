-- Prove2me | Theorems.Thm_lean_workbook_plus_50585
-- name    : lean_workbook_plus_50585
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/c893e75e-1a44-4e73-92bf-8a6c3fac87fb
-- statement:
--   Squaring and C-S: $\sqrt{(a^2+b^2)(a^2+c^2)}\geq a^2+bc$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50585 (a b c : ℝ) : Real.sqrt ((a^2 + b^2) * (a^2 + c^2)) ≥ a^2 + b * c   :=  by sorry
