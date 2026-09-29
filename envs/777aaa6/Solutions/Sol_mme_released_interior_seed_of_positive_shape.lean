-- Prove2me | solution 1 for mme_released_interior_seed_of_positive_shape
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T08:10:38.275599+00:00
-- url     : https://prove2.me/submissions/df937d78-6a8e-47f2-a1ff-3e57e3131372

import Definitions.Def_mme_released_interior_integer_profiles

open MME MME.ReleasedInterior MME.ReleasedGlobal

/-- Every released shape with three positive coordinates uses an interior recipe. -/
theorem solution :
    ∀ (owner : Fin 6) (s : Fin 45),
      (∀ i : Fin 3, 0 < ((shape s).val i).val) → (seed owner s).boundary = [] := by
  decide +kernel


#print axioms solution
