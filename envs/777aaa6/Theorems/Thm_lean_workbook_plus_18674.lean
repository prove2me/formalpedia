-- Prove2me | Theorems.Thm_lean_workbook_plus_18674
-- name    : lean_workbook_plus_18674
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/57e66105-df0a-415a-b0ac-a6f2915cc4fb
-- statement:
--   Prove or find the counterexample:\n\n$x^6 + y^6 + 4x^3y^3 >= 3y^4x^2 + 3x^4y^2$\n\n$x, y$ are positive reals.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18674 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x^6 + y^6 + 4 * (x^3 * y^3) ≥ 3 * (y^4 * x^2 + x^4 * y^2)   :=  by sorry
