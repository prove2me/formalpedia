-- Prove2me | solution 1 for Couret.STROBO2TORS.group_card_eq_h_mul_doublingImages
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:48:33.169196+00:00
-- url     : https://prove2.me/submissions/785e998f-52b3-44de-816d-efdc8b639723

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_doublingFibre_eq_image
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]









































theorem doublingFibre_card (a : G) :
    ((Finset.univ : Finset G).filter (fun x => x + x = a + a)).card =
      (twoTorsion : Finset G).card := by
  rw [doublingFibre_eq_image]
  exact Finset.card_image_of_injective twoTorsion (fun _ _ h => add_left_cancel h)

theorem p2m_local_group_card_eq_h_mul_doublingImages :
    Fintype.card G = (twoTorsion : Finset G).card * (doublingImages : Finset G).card := by
  calc
    Fintype.card G = ∑ y ∈ (doublingImages : Finset G),
        ((Finset.univ : Finset G).filter (fun x => x + x = y)).card := by
      exact (Finset.card_univ (α := G)).symm.trans
        (Finset.card_eq_sum_card_image (fun x : G => x + x) Finset.univ)
    _ = ∑ _y ∈ (doublingImages : Finset G), (twoTorsion : Finset G).card := by
      apply Finset.sum_congr rfl
      intro y hy
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hy
      rw [← ha]
      exact doublingFibre_card a
    _ = (doublingImages : Finset G).card * (twoTorsion : Finset G).card := by simp
    _ = (twoTorsion : Finset G).card * (doublingImages : Finset G).card := Nat.mul_comm _ _













































end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat (@Fintype.card.{p2m_u_0} G inst_2)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
      (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.doublingImages.{p2m_u_0} G inst inst_1 inst_2))) := @_root_.Couret.STROBO2TORS.p2m_local_group_card_eq_h_mul_doublingImages

