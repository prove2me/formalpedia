-- Prove2me | solution 1 for mme_N2_occ_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-18T18:52:11.979498+00:00
-- url     : https://prove2.me/submissions/da2f4dcd-06cb-4e29-8a52-0c34c46c41ae

import Theorems.Thm_mme_N2_total_occurrences_eq_one
import Definitions.Def_mme_integer_regional_CW_recipe
import Mathlib.Tactic

open scoped BigOperators

set_option autoImplicit false

theorem solution : forall (lower : Nat)
    (S : MME.RegionRealization.IntegerStep lower 2 (fun _ _ => True))
    (r : Fin S.R), S.n r = 1 := by
  intro lower S r
  have hsum := mme_N2_total_occurrences_eq_one lower S
  have h1 : 1 ≤ S.n r := by
    have h1 := S.parent_size r
    have h0 := S.minimum_pos
    omega
  have h2 : S.n r ≤ ∑ s, S.n s :=
    Finset.single_le_sum (fun s _ => Nat.zero_le _) (Finset.mem_univ r)
  omega
