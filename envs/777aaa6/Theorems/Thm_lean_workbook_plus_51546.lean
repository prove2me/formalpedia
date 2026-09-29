-- Prove2me | Theorems.Thm_lean_workbook_plus_51546
-- name    : lean_workbook_plus_51546
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/4acfdd67-bb75-4f71-aebe-5d87e3efd1d2
-- statement:
--   Let $x,y,z\geq 0$ ,prove that: $(x^3+y^3+z^3)(x+y+z)\geq (x^2+y^2+z^2)^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51546 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : (x^3 + y^3 + z^3) * (x + y + z) ≥ (x^2 + y^2 + z^2)^2   :=  by sorry
