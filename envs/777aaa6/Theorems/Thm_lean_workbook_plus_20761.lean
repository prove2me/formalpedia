-- Prove2me | Theorems.Thm_lean_workbook_plus_20761
-- name    : lean_workbook_plus_20761
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/0dd0aa41-a7e7-47b7-bb4b-f83ccd6c86e8
-- statement:
--   Let $z=m^{2} -1$. \n\n$z( z+1)( z+2)( z+3) =\left( 3m^{2} k^{2} -3mk\right)^{2} +\left( 3mk^{2} +3km^{2}\right)^{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20761 : ∀ m k z : ℂ,  z = m^2 - 1 → z * (z + 1) * (z + 2) * (z + 3) = (3 * m^2 * k^2 - 3 * m * k)^2 + (3 * m * k^2 + 3 * k * m^2)^2   :=  by sorry
