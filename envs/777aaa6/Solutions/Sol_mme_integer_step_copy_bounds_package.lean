-- Prove2me | solution 1 for mme_integer_step_copy_bounds_package
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-18T16:49:53.741028+00:00
-- url     : https://prove2.me/submissions/b910a94b-a9e6-4dd4-a813-6198ab6a6d9f

import Theorems.Thm_mme_integer_step_entropyCopies_le_floor
import Theorems.Thm_mme_integer_step_eight_pow_repairExponent_ge
import Definitions.Def_mme_regional_entropy_copy_bound
import Definitions.Def_mme_recursive_profiled_CW_data

set_option autoImplicit false

theorem solution : forall {ell M : Nat} {P : MME.ProfiledCW.Predicate M}
    (S : MME.RegionRealization.IntegerStep ell M P),
    S.entropyCopies ≤ ⌊S.entropyLower⌋₊ ∧ 8 ≤ 8 ^ S.repairExponent := by
  intro ell M P S
  exact ⟨mme_integer_step_entropyCopies_le_floor S,
    mme_integer_step_eight_pow_repairExponent_ge S⟩
