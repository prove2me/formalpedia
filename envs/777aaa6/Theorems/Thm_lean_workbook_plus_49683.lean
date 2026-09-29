-- Prove2me | Theorems.Thm_lean_workbook_plus_49683
-- name    : lean_workbook_plus_49683
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/8d3cd402-82a8-4d40-a1e5-f1b59de7c20f
-- statement:
--   Let $ f(x) = \dfrac{2x + 5}{x + 2} = 2 + \dfrac{1}{x + 2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49683 (x : ℝ) (hx : x ≠ -2) : (2 * x + 5) / (x + 2) = 2 + 1 / (x + 2)   :=  by sorry
