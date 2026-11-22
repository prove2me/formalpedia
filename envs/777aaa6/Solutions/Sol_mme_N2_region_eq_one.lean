-- Prove2me | solution 1 for mme_N2_region_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-18T18:29:14.89121+00:00
-- url     : https://prove2.me/submissions/45ad7f08-259d-4512-954d-95fae5fb125e

import Theorems.Thm_mme_N2_total_occurrences_eq_one
import Definitions.Def_mme_integer_regional_CW_recipe
import Mathlib.Tactic

open scoped BigOperators

set_option autoImplicit false

theorem solution : forall (lower : Nat)
    (S : MME.RegionRealization.IntegerStep lower 2 (fun _ _ => True)),
    S.R = 1 := by
  intro lower S
  have hsum := mme_N2_total_occurrences_eq_one lower S
  have hge : S.R ≤ ∑ r, S.n r := by
    calc S.R = ∑ _r : Fin S.R, 1 := by simp
    _ ≤ ∑ r, S.n r := by
      apply Finset.sum_le_sum
      intro r _
      have h1 := S.parent_size r
      have h0 := S.minimum_pos
      omega
  have hne : 0 < S.R := by
    have h := (S.hashPositions 0).1.isLt
    omega
  omega
