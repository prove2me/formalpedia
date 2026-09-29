-- Prove2me | Theorems.Thm_lean_workbook_plus_49641
-- name    : lean_workbook_plus_49641
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/ced2fba7-2797-49e5-bd6d-f83fab29ff4b
-- statement:
--   Using the AM-GM Inequality, $ \frac{(xz)^{2}+(yx)^{2}+(zy)^{2}}{xyz}\geq\frac{(xz)(yx)+(yx)(zy)+(zy)(xz)}{xyz}= x+y+z\,.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49641 (x y z: ℝ) : (x * z) ^ 2 + (y * x) ^ 2 + (z * y) ^ 2 ≥ x * y * z * (x + y + z)   :=  by sorry
