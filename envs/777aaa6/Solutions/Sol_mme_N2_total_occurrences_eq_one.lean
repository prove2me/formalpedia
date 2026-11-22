-- Prove2me | solution 1 for mme_N2_total_occurrences_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-18T18:24:30.037565+00:00
-- url     : https://prove2.me/submissions/8eb8de2d-a709-4d80-8295-4951f9370bc6

import Theorems.Thm_mme_N2_step_L_eq_two
import Theorems.Thm_mme_position_card_eq
import Definitions.Def_mme_integer_regional_CW_recipe
import Mathlib.Tactic

open scoped BigOperators

set_option autoImplicit false

theorem solution : forall (lower : Nat)
    (S : MME.RegionRealization.IntegerStep lower 2 (fun _ _ => True)),
    ∑ r, S.n r = 1 := by
  intro lower S
  have hL := mme_N2_step_L_eq_two lower S
  have hc := mme_position_card_eq S.R S.n
  have he := Fintype.card_congr S.positions
  rw [Fintype.card_fin] at he
  rw [hc, hL] at he
  omega
