-- Prove2me | solution 1 for mme_released_116_regional_split_mass
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T13:08:28.254984+00:00
-- url     : https://prove2.me/submissions/dddea3ad-3aa7-494c-8c0a-104e4d4944c9

import Definitions.Def_mme_released_116_integer_profiles
open BigOperators MME MME.Released116 MME.MoreAsymmetryExactSeed MME.RecursiveYZ MME.CompleteSplit
set_option autoImplicit false

/-- Every region has the prescribed positive number of parent occurrences. -/
theorem solution :
    ∀ r : Fin 6, 0 < regionalSize r ∧ ∑ c : Split, splitCount r c = regionalSize r := by
  decide +kernel


#print axioms solution
