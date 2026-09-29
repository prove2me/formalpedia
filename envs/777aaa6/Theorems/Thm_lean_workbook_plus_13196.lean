-- Prove2me | Theorems.Thm_lean_workbook_plus_13196
-- name    : lean_workbook_plus_13196
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/21332e11-d008-430c-bfb1-ef6dd5a4a830
-- statement:
--   Solve the equation $f(x)=0$ for $f(x)=x^{2}-2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13196 (f : ℝ → ℝ) (x : ℝ) (f_def : f x = x^2 - 2) : f x = 0 ↔ x = √2 ∨ x = -√2   :=  by sorry
