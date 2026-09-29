-- Prove2me | solution 1 for mme_released_interior_boundary_classification
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T11:03:09.112655+00:00
-- url     : https://prove2.me/submissions/b8ac2543-5922-4840-a548-9b638a9ca983

import Definitions.Def_mme_released_interior_integer_profiles

set_option autoImplicit false

/-- A released recipe has no boundary term exactly when its parent shape is
positive in all three coordinates. The certificate covers every owner and shape. -/
theorem solution :
    ∀ (owner : Fin 6) (s : Fin 45),
      (MME.ReleasedInterior.seed owner s).boundary = [] ↔
        ∀ i : Fin 3, 0 < ((MME.ReleasedGlobal.shape s).val i).val := by
  decide +kernel


#print axioms solution
