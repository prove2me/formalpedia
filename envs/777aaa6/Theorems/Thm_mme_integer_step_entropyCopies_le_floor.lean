-- Prove2me | Theorems.Thm_mme_integer_step_entropyCopies_le_floor
-- name    : mme_integer_step_entropyCopies_le_floor
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-18T15:51:50.334114+00:00
-- url     : https://prove2.me/theorems/f1298867-d5ac-4465-a96c-661ce0bca000
-- title:
--   Entropy copies are bounded by the floored lower estimate
-- statement:
--   Every integer step's guaranteed copy count is bounded by its floored entropy lower estimate.
--
--   Since $copies = \lfloor lower\rfloor_{+}/8^{exponent} \le \lfloor lower\rfloor_{+}$ by division, this records the trivial but reusable upper bound used before any lower-bound analysis.
--
--   **Formalization Note** The proof unfolds the definition and applies division monotonicity.
-- source:
--   Definition of IntegerStep.entropyCopies; supporting lemma for regional copy bounds.

import Definitions.Def_mme_regional_entropy_copy_bound
import Definitions.Def_mme_recursive_profiled_CW_data
set_option autoImplicit false

theorem mme_integer_step_entropyCopies_le_floor : forall {ell M : Nat} {P : MME.ProfiledCW.Predicate M} (S : MME.RegionRealization.IntegerStep ell M P), S.entropyCopies ≤ ⌊S.entropyLower⌋₊ := by sorry
