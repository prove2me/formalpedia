-- Prove2me | Theorems.Thm_lean_workbook_plus_43093
-- name    : lean_workbook_plus_43093
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/ab2c3e82-3e8e-4949-9c11-a5004b68c188
-- statement:
--   Show that $(x+y+z)^2 \geq 339$ given $x\geq5$ , $y\geq6$ , $z\geq7$ , and $x^2+y^2+z^2\geq125$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43093 (x y z : ℝ) (hx : 5 ≤ x) (hy : 6 ≤ y) (hz : 7 ≤ z) (h : 125 ≤ x ^ 2 + y ^ 2 + z ^ 2) : 339 ≤ (x + y + z) ^ 2   :=  by sorry
