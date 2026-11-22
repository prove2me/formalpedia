-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.ordered_append_zpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:08:29.306127+00:00
-- url     : https://prove2.me/submissions/138faec7-b371-43c1-a03a-0ca2b2521c1c

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionFinite
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shift_zero
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_lower_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shift_mem_interval
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_ordered_append_pow
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_ordered_append_inv_pow
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
theorem _root_.solution (p : Fin a) (v : Lattice k) (i : Fin k) (m : ℤ)
    (hv : v ∈ B) (hm : shift v i m ∈ B) :
    conjugate (A p) (orderedWord t v * t i ^ m) =
      conjugate (A p) (orderedWord t (shift v i m)) := by
  cases m with
  | ofNat n =>
    simp only [Int.ofNat_eq_coe, zpow_natCast]
    apply ordered_append_pow A t designated B hB ht hs
    intro r hr
    apply shift_mem_interval hB v i (n : ℤ) r hv hm
    · simp
    · simpa using (show (r : ℤ) ≤ n by exact_mod_cast hr)
  | negSucc n =>
    simp only [zpow_negSucc, ← inv_pow]
    apply ordered_append_inv_pow A t designated B hB ht hs
    intro r hr
    have hm' : shift v i (-((n + 1 : ℕ) : ℤ)) ∈ B := by simpa [Int.negSucc_eq] using hm
    apply shift_mem_interval hB v i (-((n + 1 : ℕ) : ℤ)) (-(r : ℤ)) hv hm'
    · have hr' : (r : ℤ) ≤ n + 1 := by exact_mod_cast hr
      simp only [Nat.cast_add, Nat.cast_one]
      omega
    · simp
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
