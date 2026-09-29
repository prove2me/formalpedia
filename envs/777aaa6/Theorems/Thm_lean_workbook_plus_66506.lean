-- Prove2me | Theorems.Thm_lean_workbook_plus_66506
-- name    : lean_workbook_plus_66506
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/fc531b21-14e4-46c7-a84f-1659f1774ddd
-- statement:
--   Let $x,y,z$ be positive real numbers . Prove that : $\frac{x^2}{y+z} \geq \frac{4x-y-z}{4}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66506 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x^2 / (y + z)) ≥ (4 * x - y - z) / 4   :=  by sorry
