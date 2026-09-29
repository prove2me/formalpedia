-- Prove2me | solution 1 for mme_released_interior_child_mass_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:14:43.467997+00:00
-- url     : https://prove2.me/submissions/358b13d4-a2c8-4a1b-b584-2bbf654207df

import Definitions.Def_mme_released_interior_integer_profiles

open MME MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.RecursiveYZ

/-- Released region weights and complementary split weights lie in the ranges
used to control the loss of each normalized child rate. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (c : Cell 4 6 (parent s)) :
    (seed owner s).region.getD c.1.val 0 ≤ denominator ∧
      splitWeight owner s c.1 c.2 +
        splitWeight owner s c.1 (complement (parent_total s c.1) c.2) ≤ 2 * denominator := by
  revert owner s c
  decide +kernel


#print axioms solution
