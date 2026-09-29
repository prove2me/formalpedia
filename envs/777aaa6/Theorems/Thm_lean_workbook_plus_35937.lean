-- Prove2me | Theorems.Thm_lean_workbook_plus_35937
-- name    : lean_workbook_plus_35937
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/b2e2c113-67b1-4cd1-b0ce-0ba5f973aea3
-- statement:
--   Given $x, y, z$ are sides of a triangle, prove: $\frac{xyz}{(-x+y+z) (x-y+z) (x+y-z)} \geq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35937 {x y z : ℝ} (hx : 0 < x ∧ 0 < y ∧ 0 < z) (hx1 : y + z > x) (hx2 : z + x > y) (hx3 : x + y > z) : (x * y * z) / ((-x + y + z) * (x - y + z) * (x + y - z)) ≥ 1   :=  by sorry
