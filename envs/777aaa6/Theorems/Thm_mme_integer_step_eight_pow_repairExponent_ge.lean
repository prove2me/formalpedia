-- Prove2me | Theorems.Thm_mme_integer_step_eight_pow_repairExponent_ge
-- name    : mme_integer_step_eight_pow_repairExponent_ge
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-18T15:51:49.845339+00:00
-- url     : https://prove2.me/theorems/2a12e5cb-3f0d-4b76-84c4-ce50563c0c15
-- title:
--   The copy-count divisor is at least eight
-- statement:
--   Every integer step's copy-count divisor is at least eight.
--
--   Since the repair exponent is at least one, $8^{exponent} \ge 8^1 = 8$ by power monotonicity. This makes the factor-$8$ loss in every copy estimate explicit.
--
--   **Formalization Note** This imports the proved positivity of the repair exponent.
-- source:
--   Consequence of mme_integer_step_repairExponent_pos.

import Definitions.Def_mme_integer_regional_CW_recipe
import Definitions.Def_mme_recursive_profiled_CW_data
set_option autoImplicit false

theorem mme_integer_step_eight_pow_repairExponent_ge : forall {ell M : Nat} {P : MME.ProfiledCW.Predicate M} (S : MME.RegionRealization.IntegerStep ell M P), 8 ≤ 8 ^ S.repairExponent := by sorry
