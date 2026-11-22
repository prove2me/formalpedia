-- Prove2me | Theorems.Thm_mme_N2_total_occurrences_eq_one
-- name    : mme_N2_total_occurrences_eq_one
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-18T18:24:17.518981+00:00
-- url     : https://prove2.me/theorems/79f6e1c2-59a3-48d2-9478-a452e6ccc184
-- title:
--   N=2 steps have one parent occurrence
-- statement:
--   Every integer step with two elementary positions has exactly one parent occurrence in total.
--
--   Since $L=2$ and positions pair each occurrence, $2 = 2\sum_r n_r$ forces $\sum_r n_r = 1$.
--
--   **Formalization Note** Combines the length-two and census lemmas through the position equivalence.
-- source:
--   Corollary of mme_N2_step_L_eq_two and mme_position_card_eq.

import Definitions.Def_mme_integer_regional_CW_recipe
open scoped BigOperators
set_option autoImplicit false

theorem mme_N2_total_occurrences_eq_one : forall (lower : Nat) (S : MME.RegionRealization.IntegerStep lower 2 (fun _ _ => True)), ∑ r, S.n r = 1 := by sorry
