-- Prove2me | Theorems.Thm_lean_workbook_plus_65607
-- name    : lean_workbook_plus_65607
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/6f2b5e64-4a11-468f-b276-80e4e0687ac6
-- statement:
--   Let $x,y,z\geq 0$ ,prove that: $(x^2+y^2+z^2)(y^2z^2+z^2x^2+x^2y^2)\geq (x^2y+y^2z+z^2x)^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65607 (x y z : ℝ) : (x^2 + y^2 + z^2) * (y^2 * z^2 + z^2 * x^2 + x^2 * y^2) ≥ (x^2 * y + y^2 * z + z^2 * x)^2   :=  by sorry
