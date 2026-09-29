-- Prove2me | Theorems.Thm_lean_workbook_plus_30284
-- name    : lean_workbook_plus_30284
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/7d0a5c52-2d53-43e1-a83d-0b0bb79d1216
-- statement:
--   Prove that for non-negative numbers x, y, z (absolute values of a, b, c), $x^3 + y^3 + z^3 - 3xyz \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30284 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : x ^ 3 + y ^ 3 + z ^ 3 - 3 * x * y * z ≥ 0   :=  by sorry
