-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.collection_radius_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:14:32.3783+00:00
-- url     : https://prove2.me/submissions/8040e6bc-e964-4c25-b667-729c82b25828

import Definitions.Def_Kourovka_Collection_CollectionFinite
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Collection_CollectionRadius
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_collection_three_points_words
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_orderedWord_tail_prefix
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_collect_inverse
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_neg_mem_ball
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_small_mem_ball
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_abs_le_sum_box
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_add_abs_le_sum_box
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_abs_unitSign
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_ball_solid
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_blockWord_finRange
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_collect_ordered_inverse_box
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_mul
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
    Commute (A p) (conjugate (A q) ((orderedWord t u)⁻¹ * (orderedWord t v)⁻¹)) := by
  have huB := small_mem_ball hk u ρ hρ hu
  have hU0 := collect_inverse A t designated (ball ρ) (ball_solid ρ) ht hs q u huB
  by_cases hvB : v ∈ ball ρ
  · apply collection_three_points_words A t designated (ball ρ) (ball_solid ρ) ht hs
      p q (-u) (-v) (by simpa using huB) (by simpa using hvB)
      (by simpa only [← neg_add, neg_mem_ball] using huv)
      (orderedWord t u)⁻¹ (orderedWord t v)⁻¹ hU0
    simp
  have hvge : ρ ≤ ‖euclidean v‖ := le_of_not_gt hvB
  obtain ⟨j, hD, hd⟩ := exists_radius_split hk true u v ρ hρ hu hvge hv
  let c := prefixStep true v j
  let d := tailStep true v j
  let D := latticeAbs u + latticeAbs c
  have hDB : D ∈ ball ρ := hD
  have hdB : d ∈ ball ρ := hd
  have hcd : c + d = v := prefix_add_tail true v j
  have hstart : ∀ i, |(-u) i| ≤ |D i| := by simpa using abs_le_sum_box u c
  have hend : ∀ i, |(-u) i - c i| ≤ |D i| := by
    intro i
    simpa only [Pi.neg_apply, ← neg_add, sub_eq_add_neg, abs_neg] using add_abs_le_sum_box u c i
  have hx : -u - c ∈ ball ρ := ball_solid ρ _ D hDB hend
  have hy : -d ∈ ball ρ := by simpa using hdB
  have hsum : (-u - c) + -d ∈ ball ρ := by
    have he : (-u - c) + -d = -(u + v) := by rw [← hcd]; abel
    simpa only [he, neg_mem_ball] using huv
  have hU : conjugate (A q) ((orderedWord t u)⁻¹ * (orderedWord t c)⁻¹) =
      conjugate (A q) (orderedWord t (-u - c)) := by
    rw [conjugate_mul, hU0, ← conjugate_mul]
    exact collect_ordered_inverse_box A t designated (ball ρ) (ball_solid ρ) ht hs q
      (-u) c D hDB hstart hend
  have hV : conjugate (A p) ((orderedWord t d)⁻¹)⁻¹ =
      conjugate (A p) (orderedWord t (-(-d))) := by simp
  have h := collection_three_points_words A t designated (ball ρ) (ball_solid ρ) ht hs
    p q (-u - c) (-d) hx hy hsum
    ((orderedWord t u)⁻¹ * (orderedWord t c)⁻¹) (orderedWord t d)⁻¹ hU hV
  rw [orderedWord_tail_prefix t v j, mul_inv_rev, ← mul_assoc]
  exact h
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
