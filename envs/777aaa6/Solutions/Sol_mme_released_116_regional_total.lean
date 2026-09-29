-- Prove2me | solution 1 for mme_released_116_regional_total
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T13:08:31.527352+00:00
-- url     : https://prove2.me/submissions/ba8a90f9-9bad-4a40-9ec4-8a2a3666ef70

import Definitions.Def_mme_released_116_integer_profiles
open BigOperators MME MME.Released116 MME.MoreAsymmetryExactSeed MME.RecursiveYZ MME.CompleteSplit
set_option autoImplicit false

/-- Every region has the prescribed positive number of parent occurrences. -/
theorem mme_released_116_regional_split_mass :
    ∀ r : Fin 6, 0 < regionalSize r ∧ ∑ c : Split, splitCount r c = regionalSize r := by
  decide +kernel

/-- The child profile has exactly one count for each physical occurrence of
its split or its complementary split. -/
theorem mme_released_116_integer_profile_mass :
    ∀ (i : Fin 3) (c : Cell 4 6 parent),
      ∑ w, integerProfile i c w =
        splitCount c.1 c.2 + splitCount c.1 (complement (parent_total c.1) c.2) := by
  decide +kernel

/-- Positive child counts have the grade required by the integer-step interface. -/
theorem mme_released_116_integer_profile_support :
    ∀ (i : Fin 3) (c : Cell 4 6 parent) (w : CompleteWord 2),
      0 < integerProfile i c w → ∑ h, (w h).val = (c.2.val i).val := by
  decide +kernel

/-- The three forced CW boundary reversals hold for the concrete child profiles. -/
theorem mme_released_116_integer_profile_boundary : BoundaryProfiles integerProfile := by
  unfold BoundaryProfiles
  decide +kernel

/-- The six regions exhaust the released joint-row scale. -/
theorem solution :
    ∑ r, regionalSize r = denominator ^ 4 := by
  decide +kernel


#print axioms solution
