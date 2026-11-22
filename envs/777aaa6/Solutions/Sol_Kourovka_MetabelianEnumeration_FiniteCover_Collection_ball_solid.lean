-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.ball_solid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:54:39.420702+00:00
-- url     : https://prove2.me/submissions/31c8030a-cd37-42e8-84f7-1016d15cc813

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_norm_sq

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {k : ℕ} (ρ : ℝ) : Solid (ball (k := k) ρ) := by
  intro v w hw h
  have hsq : ‖euclidean v‖ ^ 2 ≤ ‖euclidean w‖ ^ 2 := by
    rw [euclidean_norm_sq, euclidean_norm_sq]
    apply Finset.sum_le_sum
    intro i _
    have hi : |(v i : ℝ)| ≤ |(w i : ℝ)| := by exact_mod_cast h i
    exact sq_le_sq.mpr hi
  have hnorm : ‖euclidean v‖ ≤ ‖euclidean w‖ := by
    nlinarith [norm_nonneg (euclidean v), norm_nonneg (euclidean w)]
  exact hnorm.trans_lt hw
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
