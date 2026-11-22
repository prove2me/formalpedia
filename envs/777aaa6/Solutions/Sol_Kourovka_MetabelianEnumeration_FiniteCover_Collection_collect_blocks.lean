-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.collect_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:09:37.753554+00:00
-- url     : https://prove2.me/submissions/80927bae-4650-431e-b0e7-e8c9acfec714

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionFinite
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shift_zero
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_lower_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_ordered_append_zpow
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shiftList_nil
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shiftList_cons
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_blockWord_finRange
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shiftList_finRange
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

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a) (B : Set (Lattice k))
    (hB : Solid B)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hs : ∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (p : Fin a) (v w : Lattice k) (l : List (Fin k)) (hl : l.Nodup)
    (d : Lattice k) (hd : d ∈ B)
    (hv : ∀ i, |v i| ≤ |d i|) (hend : ∀ i, |shiftList v w l i| ≤ |d i|) :
    conjugate (A p) (orderedWord t v * blockWord t w l) =
      conjugate (A p) (orderedWord t (shiftList v w l)) := by
  induction l generalizing v with
  | nil => simp [blockWord]
  | cons i l ih =>
    have hi : i ∉ l := (List.nodup_cons.mp hl).1
    have hl' : l.Nodup := (List.nodup_cons.mp hl).2
    have hmid : ∀ j, |shift v i (w i) j| ≤ |d j| := by
      intro j
      by_cases hj : j = i
      · subst j
        simpa [shift, shiftList] using hend i
      · simpa [shift, hj] using hv j
    have hstartB := hB v d hd hv
    have hmidB := hB (shift v i (w i)) d hd hmid
    have htail := ih (shift v i (w i)) hl' hmid (by simpa [shiftList_cons v w i l hi] using hend)
    calc
      conjugate (A p) (orderedWord t v * blockWord t w (i :: l)) =
          conjugate (conjugate (A p) (orderedWord t v * t i ^ w i)) (blockWord t w l) := by
        simp only [blockWord, List.map_cons, List.prod_cons]
        rw [← mul_assoc, conjugate_mul]
      _ = conjugate (conjugate (A p) (orderedWord t (shift v i (w i)))) (blockWord t w l) := by
        rw [ordered_append_zpow A t designated B hB ht hs p v i (w i) hstartB hmidB]
      _ = conjugate (A p) (orderedWord t (shiftList (shift v i (w i)) w l)) := by
        rw [← conjugate_mul]
        exact htail
      _ = conjugate (A p) (orderedWord t (shiftList v w (i :: l))) := by
        rw [shiftList_cons v w i l hi]
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
