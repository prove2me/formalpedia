-- Prove2me | Theorems.Thm_lean_workbook_plus_37022
-- name    : lean_workbook_plus_37022
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/c5da3f19-340c-452a-a73f-4eea6ebddd96
-- statement:
--   $\left(a,-\frac 1{a+1},-\frac{a+1}a\right)$ for any real $a\ne 0,-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37022 (a : ℝ) (ha : a ≠ 0) (ha' : a ≠ -1) : ∃ x y z : ℝ, x = a ∧ y = -1/(a+1) ∧ z = -(a+1)/a   :=  by sorry
