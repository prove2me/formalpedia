-- Prove2me | Theorems.Thm_lean_workbook_plus_28770
-- name    : lean_workbook_plus_28770
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/99f6d3cb-e242-478d-9b59-76fe95732fb7
-- statement:
--   For any positive numbers $x$ and $y$ such that $x \geq y$ , we have $x^x y^y \geq x^y y^x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28770 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x ≥ y) : x^x * y^y ≥ x^y * y^x   :=  by sorry
