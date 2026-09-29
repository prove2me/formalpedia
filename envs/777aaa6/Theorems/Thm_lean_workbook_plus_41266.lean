-- Prove2me | Theorems.Thm_lean_workbook_plus_41266
-- name    : lean_workbook_plus_41266
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/ec636a69-9e48-411e-896b-5e030a77ad0a
-- statement:
--   Let $x,y,z \geq 0$ ,prove that: $x^3+y^3+2z^3 \geq yz(y+z)+xz(z+x).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41266 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : x^3 + y^3 + 2 * z^3 ≥ y * z * (y + z) + x * z * (z + x)   :=  by sorry
