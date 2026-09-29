-- Prove2me | Theorems.Thm_lean_workbook_plus_50206
-- name    : lean_workbook_plus_50206
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/71ec5da6-24ff-431a-8c98-5102974b62d9
-- statement:
--   Solve the equation $x^2 + x - \dfrac{3}{4} = 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50206 (x : ℝ) : x^2 + x - 3/4 = 0 ↔ x = 1/2 ∨ x = -3/2   :=  by sorry
