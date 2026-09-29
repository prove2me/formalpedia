-- Prove2me | Theorems.Thm_lean_workbook_plus_1311
-- name    : lean_workbook_plus_1311
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/cb3dd3ac-ff76-4fb8-b14c-4d9e5ee9d67e
-- statement:
--   $\frac{x}{y}+\frac{y}{z}+\frac{z}{x}\geq 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1311 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 3 ≤ x / y + y / z + z / x   :=  by sorry
