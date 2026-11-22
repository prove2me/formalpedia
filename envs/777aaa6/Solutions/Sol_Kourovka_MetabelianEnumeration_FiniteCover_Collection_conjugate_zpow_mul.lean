-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_zpow_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:04:02.265339+00:00
-- url     : https://prove2.me/submissions/af16f59c-1319-4fb0-8a72-1f186a178ca9

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_Kourovka_Collection_Collection
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_pow_mul
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_inv_pow_mul
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_one

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution (x t c : G) (m : ℤ)
    (h : ∀ r : ℤ, |r| ≤ |m| → Commute c (conjugate x (t ^ r))) :
    conjugate x ((t * c) ^ m) = conjugate x (t ^ m) := by
  cases m with
  | ofNat n =>
    simp only [Int.ofNat_eq_coe, zpow_natCast]
    apply conjugate_pow_mul
    intro r hr
    simpa using h (r : ℤ) (by simpa using (show (r : ℤ) ≤ n by exact_mod_cast hr))
  | negSucc n =>
    simp only [zpow_negSucc, ← inv_pow]
    apply conjugate_inv_pow_mul
    intro r hr
    have hb : |-(r : ℤ)| ≤ |Int.negSucc n| := by
      simpa only [abs_neg, Int.abs_natCast, Int.negSucc_eq, abs_neg] using
        (show (r : ℤ) ≤ n + 1 by exact_mod_cast hr)
    simpa only [zpow_neg, zpow_natCast, inv_pow] using h (-(r : ℤ)) hb
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
