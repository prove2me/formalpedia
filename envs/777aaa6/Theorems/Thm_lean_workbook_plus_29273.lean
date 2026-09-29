-- Prove2me | Theorems.Thm_lean_workbook_plus_29273
-- name    : lean_workbook_plus_29273
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/b49df92c-7e5b-45a1-977e-958bea959c7b
-- statement:
--   $X^2<XY<\frac{1}{100}$ $\Rightarrow$ $X<\frac{1}{10}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29273 (x y : ℝ) (h : x ^ 2 < x * y ∧ x * y < 1 / 100) : x < 1 / 10   :=  by sorry
