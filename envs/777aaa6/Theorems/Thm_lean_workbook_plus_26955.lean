-- Prove2me | Theorems.Thm_lean_workbook_plus_26955
-- name    : lean_workbook_plus_26955
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/cc40f7d7-d28d-45b9-8733-9dcece4f0554
-- statement:
--   $\\sin^2(nx) = \\frac{1}{2}\\left(1- \\cos(2nx) \\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26955 (n : ℕ) (x : ℝ) : (sin (n * x))^2 = 1 / 2 * (1 - cos (2 * n * x))   :=  by sorry
