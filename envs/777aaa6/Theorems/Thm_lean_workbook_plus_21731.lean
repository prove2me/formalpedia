-- Prove2me | Theorems.Thm_lean_workbook_plus_21731
-- name    : lean_workbook_plus_21731
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/7a5f3844-07f6-4c16-8709-d217c0cd8e66
-- statement:
--   Show that $\left ( {\frac{a+b}{2}} \right )^2 > ab, \quad |a| \ne b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21731 (a b : ℝ) (h1 : a ≠ b) (h2 : a ≠ -b) : (a + b) ^ 2 / 4 > a * b   :=  by sorry
