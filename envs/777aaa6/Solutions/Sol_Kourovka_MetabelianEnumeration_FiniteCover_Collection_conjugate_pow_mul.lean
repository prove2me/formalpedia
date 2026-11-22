-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:03:03.231111+00:00
-- url     : https://prove2.me/submissions/0a41f09a-33f2-44d4-9973-ad10da47c61a

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
    (h : ∀ r : ℕ, r ≤ n → Commute c (conjugate x (t ^ r))) :
    conjugate x ((t * c) ^ n) = conjugate x (t ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := ih (fun r hr => h r (hr.trans (Nat.le_succ n)))
    calc
      conjugate x ((t * c) ^ (n + 1)) =
          conjugate (conjugate x (t ^ n)) (t * c) := by
        rw [pow_succ, conjugate_mul, hn]
      _ = conjugate (conjugate x (t ^ (n + 1))) c := by
        simp only [pow_succ, conjugate_mul]
      _ = conjugate x (t ^ (n + 1)) := conjugate_eq_self (h (n + 1) le_rfl)
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
