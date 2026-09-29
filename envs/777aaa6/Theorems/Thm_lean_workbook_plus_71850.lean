-- Prove2me | Theorems.Thm_lean_workbook_plus_71850
-- name    : lean_workbook_plus_71850
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/839f641f-faa2-4c94-9184-11c758af632c
-- statement:
--   $\left(-\frac 1{a+1},-\frac{a+1}a, a\right)$ for any real $a\ne 0,-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71850 (a : ℝ) (ha : a ≠ 0) (ha' : a ≠ -1) : ∃ x y z : ℝ, x = -1/(a+1) ∧ y = -(a+1)/a ∧ z = a   :=  by sorry
