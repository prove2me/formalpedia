-- Prove2me | Theorems.Thm_lean_workbook_plus_43259
-- name    : lean_workbook_plus_43259
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/8eabfa34-0bfe-4891-9b1f-69c6133b3175
-- statement:
--   Prove that $x^2+y^2+z^2\geq xy+yz+xz$ for positive reals $x, y, z$ such that $xyz=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43259 (x y z : ℝ) (h : x*y*z = 1) : x^2 + y^2 + z^2 ≥ x*y + y*z + x*z   :=  by sorry
