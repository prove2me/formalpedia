-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.collection_three_points
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:12:17.106068+00:00
-- url     : https://prove2.me/submissions/4c8d3aea-8c3d-46b9-a297-8b6764c837bb

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionFinite
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shift_zero
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_lower_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shiftList_nil
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_blockWord_finRange
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shiftList_finRange
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_collect_ordered_box
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_orderedWord_zero
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_collect_ordered_inverse_box
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_commute_conjugate_iff
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_mul
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_lower
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_castSucc
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_last
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_one
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_lower
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_castSucc
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_last


attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.shift_zero
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_shift
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.lower_shift
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.shiftList_nil
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.blockWord_finRange
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.shiftList_finRange
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.orderedWord_zero

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a) (B : Set (Lattice k))
    (hB : Solid B)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hs : ∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (p q : Fin a) (x y : Lattice k) (hx : x ∈ B) (hy : y ∈ B) (hxy : x + y ∈ B) :
    Commute (A p) (conjugate (A q) (orderedWord t x * orderedWord t y)) := by
  let c : Lattice k := fun i => if |x i + y i| ≤ |x i| then y i else 0
  let d := y - c
  have hcd : c + d = y := by dsimp [d]; abel
  have hcabs : ∀ i, |c i| ≤ |y i| := by
    intro i; dsimp [c]; split <;> simp
  have hdabs : ∀ i, |d i| ≤ |y i| := by
    intro i; dsimp [d, c]; split <;> simp
  have hxc : ∀ i, |x i + c i| ≤ |x i| := by
    intro i; dsimp [c]; split <;> rename_i h <;> simp [h]
  have hxcend : ∀ i, |x i + c i| ≤ |x i + y i| := by
    intro i; dsimp [c]; split <;> simp
    omega
  have hsum : x + c + d = x + y := by rw [add_assoc, hcd]
  have hneg : -d - c = -y := by rw [sub_eq_add_neg, ← neg_add, add_comm d c, hcd]
  have hfirst := collect_ordered_box A t designated B hB ht hs q x c x hx (fun _ => le_rfl) hxc
  have hsecond := collect_ordered_box A t designated B hB ht hs q (x + c) d (x + y) hxy
    hxcend (by intro i; simpa only [← Pi.add_apply, hsum] using (le_refl |(x + y) i|))
  have hcollect : conjugate (A q) (orderedWord t x * (orderedWord t c * orderedWord t d)) =
      conjugate (A q) (orderedWord t (x + y)) := by
    rw [← mul_assoc, conjugate_mul, hfirst, ← conjugate_mul, hsecond, hsum]
  have hay := collect_ordered_inverse_box A t designated B hB ht hs p 0 y y hy
    (by intro i; simp) (by intro i; simp)
  have had := collect_ordered_inverse_box A t designated B hB ht hs p 0 d y hy
    (by intro i; simp) (by simpa using hdabs)
  have hac := collect_ordered_inverse_box A t designated B hB ht hs p (-d) c y hy
    (by simpa using hdabs) (by
      intro i
      change |(-d - c) i| ≤ |y i|
      rw [hneg]
      simp)
  simp only [orderedWord_zero, one_mul, zero_sub] at hay had
  have haw : conjugate (A p) (orderedWord t c * orderedWord t d)⁻¹ =
      conjugate (A p) (orderedWord t (-y)) := by
    rw [mul_inv_rev, conjugate_mul, had, ← conjugate_mul, hac, hneg]
  have hcomm := hs p q (x + y) hxy
  rw [← hcollect, conjugate_mul] at hcomm
  have hpair := (commute_conjugate_iff (A p) (conjugate (A q) (orderedWord t x))
    (orderedWord t c * orderedWord t d)).mp hcomm
  rw [haw, ← hay] at hpair
  rw [conjugate_mul]
  exact (commute_conjugate_iff _ _ _).mpr hpair
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
