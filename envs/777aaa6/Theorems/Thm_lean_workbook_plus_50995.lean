-- Prove2me | Theorems.Thm_lean_workbook_plus_50995
-- name    : lean_workbook_plus_50995
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/bd01d7b3-72de-4bf2-bb58-31181830e64a
-- statement:
--   Let $x, y$ be real numbers such that $xy+(x+y)(3-2x-2y)=1.$ Prove that $-1\leq x^2-y^2\leq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50995 (x y : ℝ) (h : x * y + (x + y) * (3 - 2 * x - 2 * y) = 1) :
  -1 ≤ x^2 - y^2 ∧ x^2 - y^2 ≤ 1   :=  by sorry
