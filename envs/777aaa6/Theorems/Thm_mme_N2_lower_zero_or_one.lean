-- Prove2me | Theorems.Thm_mme_N2_lower_zero_or_one
-- name    : mme_N2_lower_zero_or_one
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-18T17:24:21.318185+00:00
-- url     : https://prove2.me/theorems/681d51e8-8495-4046-812b-50b2fb41dbd0
-- title:
--   N=2 steps are at level 0 or 1
-- statement:
--   Every integer step with two elementary positions is at level $0$ or level $1$.
--
--   This is the case-split form of the level bound $lower < 2$: whoever proves the five-copy or boundary-match leaves only needs the two small cases.
--
--   **Formalization Note** Direct corollary of the proved level bound.
-- source:
--   Corollary of mme_entropy_regional_step_N2_lt_two; case split for the regional leaves.

import Definitions.Def_mme_integer_regional_CW_recipe
set_option autoImplicit false

theorem mme_N2_lower_zero_or_one : forall (lower : Nat) (S : MME.RegionRealization.IntegerStep lower 2 (fun _ _ => True)), lower = 0 ∨ lower = 1 := by sorry
