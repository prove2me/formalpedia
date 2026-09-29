-- Prove2me | Theorems.Thm_lean_workbook_plus_57100
-- name    : lean_workbook_plus_57100
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/fedb2f2e-4e18-42b2-9481-734a1a0fe2b1
-- statement:
--   Solve $x=y^2+z^2, y=z^2+x^2, z=x^2+y^2$ in the reals.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57100 (x y z : ℝ) (hx : x = y ^ 2 + z ^ 2) (hy : y = z ^ 2 + x ^ 2) (hz : z = x ^ 2 + y ^ 2) : x = y ∧ y = z ∧ z = x   :=  by sorry
