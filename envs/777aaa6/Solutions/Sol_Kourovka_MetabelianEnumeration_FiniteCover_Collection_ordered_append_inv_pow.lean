-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.ordered_append_inv_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:07:18.873184+00:00
-- url     : https://prove2.me/submissions/47c7fddd-ced0-4a93-a18a-a3ee5b91184e

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionFinite
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shift_zero
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_lower_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_mul
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_ordered_insert_inv
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

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
variable {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
  (designated : Fin k → Fin k → Fin a) (B : Set (Lattice k))
  (hB : Solid B)
  (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
  (hs : ∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v)))
include hB ht hs
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution (p : Fin a) (v : Lattice k) (i : Fin k) (n : ℕ)
    (h : ∀ r : ℕ, r ≤ n → shift v i (-(r : ℤ)) ∈ B) :
    conjugate (A p) (orderedWord t v * (t i)⁻¹ ^ n) =
      conjugate (A p) (orderedWord t (shift v i (-(n : ℤ)))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := ih (fun r hr => h r (hr.trans (Nat.le_succ n)))
    calc
      conjugate (A p) (orderedWord t v * (t i)⁻¹ ^ (n + 1)) =
          conjugate (conjugate (A p) (orderedWord t v * (t i)⁻¹ ^ n)) (t i)⁻¹ := by
        rw [pow_succ, ← mul_assoc, conjugate_mul]
      _ = conjugate (A p) (orderedWord t (shift v i (-(n : ℤ))) * (t i)⁻¹) := by
        rw [hn, conjugate_mul]
      _ = conjugate (A p) (orderedWord t (shift v i (-((n + 1 : ℕ) : ℤ)))) := by
        have hi := ordered_insert_inv A t designated B hB ht hs p (shift v i (-(n : ℤ))) i
          (h n (Nat.le_succ n)) (by simpa [sub_eq_add_neg, neg_add, add_comm] using h (n + 1) le_rfl)
        simpa [sub_eq_add_neg, neg_add, add_comm] using hi
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
