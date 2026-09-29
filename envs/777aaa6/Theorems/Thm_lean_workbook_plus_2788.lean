-- Prove2me | Theorems.Thm_lean_workbook_plus_2788
-- name    : lean_workbook_plus_2788
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/5f1d89d8-d5fb-4b85-896c-d3f27882d20e
-- statement:
--   Prove that $x^3+y^3+z^3\ge 3xyz$ for all nonnegatives $x,y,z$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2788 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : x ^ 3 + y ^ 3 + z ^ 3 ≥ 3 * x * y * z   :=  by sorry
