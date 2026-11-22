-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_inv_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:03:15.299188+00:00
-- url     : https://prove2.me/submissions/148a77fa-6471-4866-84df-a3fe3b40556f

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_Kourovka_Collection_Collection
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_mul
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_eq_self
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_one

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution (x t c : G) (n : ℕ)
    (h : ∀ r : ℕ, r ≤ n → Commute c (conjugate x (t⁻¹ ^ r))) :
    conjugate x ((t * c)⁻¹ ^ n) = conjugate x (t⁻¹ ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := ih (fun r hr => h r (hr.trans (Nat.le_succ n)))
    calc
      conjugate x ((t * c)⁻¹ ^ (n + 1)) =
          conjugate (conjugate x (t⁻¹ ^ n)) (c⁻¹ * t⁻¹) := by
        rw [pow_succ, conjugate_mul, hn, mul_inv_rev]
      _ = conjugate (conjugate x (t⁻¹ ^ n)) t⁻¹ := by
        rw [conjugate_mul, conjugate_eq_self (h n (Nat.le_succ n)).inv_left]
      _ = conjugate x (t⁻¹ ^ (n + 1)) := by rw [pow_succ, conjugate_mul]
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
