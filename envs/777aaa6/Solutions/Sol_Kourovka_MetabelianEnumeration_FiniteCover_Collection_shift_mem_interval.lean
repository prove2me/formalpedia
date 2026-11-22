-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.shift_mem_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:04:23.065617+00:00
-- url     : https://prove2.me/submissions/5635dc2f-0252-4b0e-a902-3b331d5a4d73

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionFinite
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shift_zero
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_lower_shift
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
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {k : ℕ} {B : Set (Lattice k)} (hB : Solid B)
    (v : Lattice k) (i : Fin k) (m r : ℤ) (hv : v ∈ B) (hm : shift v i m ∈ B)
    (hr : min 0 m ≤ r) (hr' : r ≤ max 0 m) : shift v i r ∈ B := by
  have habs : |v i + r| ≤ max |v i| |v i + m| := by
    apply abs_le.mpr
    have h0 := le_max_left |v i| |v i + m|
    have h1 := le_max_right |v i| |v i + m|
    have h2 := le_abs_self (v i)
    have h3 := neg_abs_le (v i)
    have h4 := le_abs_self (v i + m)
    have h5 := neg_abs_le (v i + m)
    by_cases h : 0 ≤ m
    · simp only [min_eq_left h, max_eq_right h] at hr hr'
      constructor <;> omega
    · have h : m ≤ 0 := by omega
      simp only [min_eq_right h, max_eq_left h] at hr hr'
      constructor <;> omega
  by_cases h : |v i + m| ≤ |v i|
  · apply hB _ _ hv
    intro j
    by_cases hj : j = i
    · subst j
      simpa [shift, max_eq_left h] using habs
    · simp [shift, hj]
  · have h : |v i| ≤ |v i + m| := by omega
    apply hB _ _ hm
    intro j
    by_cases hj : j = i
    · subst j
      simpa [shift, max_eq_right h] using habs
    · simp [shift, hj]
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
