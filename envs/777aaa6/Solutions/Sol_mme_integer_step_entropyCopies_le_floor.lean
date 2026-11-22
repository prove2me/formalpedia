-- Prove2me | solution 1 for mme_integer_step_entropyCopies_le_floor
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-18T15:52:22.649897+00:00
-- url     : https://prove2.me/submissions/10c813ab-a41c-4624-93b5-04beb9f7cfae

import Definitions.Def_mme_regional_entropy_copy_bound
import Definitions.Def_mme_recursive_profiled_CW_data

set_option autoImplicit false

theorem solution : forall {ell M : Nat} {P : MME.ProfiledCW.Predicate M}
    (S : MME.RegionRealization.IntegerStep ell M P),
    S.entropyCopies ≤ ⌊S.entropyLower⌋₊ := by
  intro ell M P S
  unfold MME.RegionRealization.IntegerStep.entropyCopies
  exact Nat.div_le_self _ _
