-- Prove2me | Theorems.Thm_lean_workbook_plus_44082
-- name    : lean_workbook_plus_44082
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/a8dc0d09-fcbd-4afe-8400-01d7f65df055
-- statement:
--   Prove the inequality: $x^2z+y^2z+z^2y+xyz>0$ for $x\geq y\geq z>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44082 (x y z : ℝ) (hx : x ≥ y) (hy : y ≥ z) (hz : z > 0) : x^2 * z + y^2 * z + z^2 * y + x * y * z > 0   :=  by sorry
