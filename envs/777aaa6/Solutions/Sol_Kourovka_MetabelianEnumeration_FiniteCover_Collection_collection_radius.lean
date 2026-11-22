-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.collection_radius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:14:31.910938+00:00
-- url     : https://prove2.me/submissions/002301dd-6e24-4929-bd02-a18a971bd197

import Definitions.Def_Kourovka_Collection_CollectionFinite
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Collection_CollectionRadius
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_collection_three_points_words
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_orderedWord_prefix_tail
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_collect_inverse
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_neg_mem_ball
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_small_mem_ball
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_abs_le_sum_box
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_add_abs_le_sum_box
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_abs_unitSign
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_ball_solid
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_blockWord_finRange
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_collect_ordered_box
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_collection_three_points
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_add
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_neg
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_norm_abs
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_exists_radius_split
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_lower_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_not_precedes_self
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_orderedWord_zero
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_prefix_add_tail
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_lower
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_castSucc
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_last
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shiftList_finRange
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shiftList_nil
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shift_zero
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.abs_unitSign
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.blockWord_finRange
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_one
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_add
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_neg
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_norm_abs
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.lower_shift
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.not_precedes_self
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.orderedWord_zero
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_lower
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_shift
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_castSucc
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_last
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.shiftList_finRange
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.shiftList_nil
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.shift_zero


attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.neg_mem_ball

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a) (hk : 1 ≤ k) (ρ : ℝ)
    (hρ : 2 * (k : ℝ) < ρ)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hs : ∀ p q v, v ∈ ball ρ → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (p q : Fin a) (u v : Lattice k)
    (hu : ‖euclidean u‖ ≤ ρ / (2 * k))
    (hv : ‖euclidean v‖ < ρ + 1 / (2 * k))
    (huv : ‖euclidean (u + v)‖ < ρ) :
    Commute (A p) (conjugate (A q) (orderedWord t u * orderedWord t v)) := by
  have huB := small_mem_ball hk u ρ hρ hu
  by_cases hvB : v ∈ ball ρ
  · exact collection_three_points A t designated (ball ρ) (ball_solid ρ) ht hs
      p q u v huB hvB huv
  have hvge : ρ ≤ ‖euclidean v‖ := le_of_not_gt hvB
  obtain ⟨j, hD, hd⟩ := exists_radius_split hk false u v ρ hρ hu hvge hv
  let c := prefixStep false v j
  let d := tailStep false v j
  let D := latticeAbs u + latticeAbs c
  have hDB : D ∈ ball ρ := hD
  have hdB : d ∈ ball ρ := hd
  have hcd : c + d = v := prefix_add_tail false v j
  have huc : u + c ∈ ball ρ :=
    ball_solid ρ _ D hDB (add_abs_le_sum_box u c)
  have hsum : (u + c) + d ∈ ball ρ := by simpa only [add_assoc, hcd] using huv
  have hU := collect_ordered_box A t designated (ball ρ) (ball_solid ρ) ht hs q u c D hDB
    (abs_le_sum_box u c) (add_abs_le_sum_box u c)
  have hV := collect_inverse A t designated (ball ρ) (ball_solid ρ) ht hs p d hdB
  have h := collection_three_points_words A t designated (ball ρ) (ball_solid ρ) ht hs
    p q (u + c) d huc hdB hsum (orderedWord t u * orderedWord t c) (orderedWord t d) hU hV
  rw [orderedWord_prefix_tail t v j, ← mul_assoc]
  exact h
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
