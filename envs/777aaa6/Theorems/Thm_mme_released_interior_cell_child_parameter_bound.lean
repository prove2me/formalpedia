-- Prove2me | Theorems.Thm_mme_released_interior_cell_child_parameter_bound
-- name    : mme_released_interior_cell_child_parameter_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:13:40.396494+00:00
-- url     : https://prove2.me/theorems/c7ddea43-1da4-4c04-a7b5-92848759b12d
-- title:
--   Released cell parameters lie in the entropy domain
-- statement:
--   The existing universal child lookup bound implies that twice the parameter of every actual released child cell is at most the common denominator. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_interior_child_parameter_bound
open MME MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.RecursiveYZ

theorem mme_released_interior_cell_child_parameter_bound
    (owner : Fin 6) (s : Fin 45) (c : Cell 4 6 (parent s)) :
    2 * ((((seed owner s).children.find?
      (fun a ↦ a.1 == c.1.val && a.2.1 == sourceShape owner c.2)).getD
        (0, [], 0)).2.2) ≤ denominator := by sorry
