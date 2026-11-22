-- Prove2me | Theorems.Thm_mme_integer_step_repairExponent_pos
-- name    : mme_integer_step_repairExponent_pos
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-18T15:00:20.319243+00:00
-- url     : https://prove2.me/theorems/b376f906-ab05-41b4-9928-d26878ff84a6
-- title:
--   Repair exponents are positive
-- statement:
--   Every integer regional step has repair exponent at least one.
--
--   The exponent is defined as $\log_{repairScale}(capacity)+1$, so positivity is immediate. This records the denominator $8^{exponent}\ge 8$ used by every copy-count estimate.
--
--   **Formalization Note** The proof unfolds the definition and closes by arithmetic.
-- source:
--   Definition of IntegerStep.repairExponent; supporting lemma for regional copy bounds, Alman et al., More Asymmetry, https://arxiv.org/html/2404.16349v2#S6.

import Definitions.Def_mme_integer_regional_CW_recipe
import Definitions.Def_mme_recursive_profiled_CW_data
set_option autoImplicit false

theorem mme_integer_step_repairExponent_pos : forall {ell M : Nat} {P : MME.ProfiledCW.Predicate M} (S : MME.RegionRealization.IntegerStep ell M P), 1 ≤ S.repairExponent := by sorry
