-- Prove2me | solution 1 for mme_released_interior_cell_child_parameter_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:14:44.861993+00:00
-- url     : https://prove2.me/submissions/cbd0187d-1b61-406b-9392-c0dc469d5d19

import Theorems.Thm_mme_released_interior_child_parameter_bound

open MME MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.RecursiveYZ

/-- Every released child parameter lies in the range required by the physical
112 dimension formula, including missing entries whose parameter defaults to zero. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (c : Cell 4 6 (parent s)) :
    2 * ((((seed owner s).children.find?
      (fun a ↦ a.1 == c.1.val && a.2.1 == sourceShape owner c.2)).getD
        (0, [], 0)).2.2) ≤ denominator := by
  have h := mme_released_interior_child_parameter_bound owner s c.1 (sourceShape owner c.2)
  omega


#print axioms solution
