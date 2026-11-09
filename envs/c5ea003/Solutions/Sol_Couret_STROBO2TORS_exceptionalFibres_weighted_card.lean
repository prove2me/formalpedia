-- Prove2me | solution 1 for Couret.STROBO2TORS.exceptionalFibres_weighted_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:12:28.442635+00:00
-- url     : https://prove2.me/submissions/d3799733-940f-4a25-9d82-6a81f34d4d33

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_member_card
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_preimage
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupports_card
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]

































/-- Exact cross-multiplied count of exceptional fibres. -/
theorem p2m_local_exceptionalFibres_weighted_card :
    (2 * (twoTorsion : Finset G).card) *
      (exceptionalFibres : Finset (Finset (Finset G))).card =
      Fintype.card G * ((twoTorsion : Finset G).card - 1) * ((threeTorsion : Finset G).card - 1) := by
  have hc : (exceptionalSupports : Finset (Finset G)).card =
      (2 * (twoTorsion : Finset G).card) * (exceptionalFibres (G := G)).card := by
    calc
      (exceptionalSupports : Finset (Finset G)).card =
          ∑ F ∈ (exceptionalFibres (G := G)),
            ((exceptionalSupports (G := G)).filter (fun S => squareFibre S = F)).card :=
        Finset.card_eq_sum_card_image (squareFibre (G := G)) (exceptionalSupports (G := G))
      _ = ∑ _F ∈ (exceptionalFibres (G := G)), 2 * (twoTorsion : Finset G).card := by
        apply Finset.sum_congr rfl
        intro F hF
        rw [exceptionalFibres_preimage F hF]
        exact exceptionalFibres_member_card F hF
      _ = (exceptionalFibres (G := G)).card * (2 * (twoTorsion : Finset G).card) := by simp
      _ = (2 * (twoTorsion : Finset G).card) * (exceptionalFibres (G := G)).card := Nat.mul_comm _ _
  rw [← hc, exceptionalSupports_card]























































end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Couret.STROBO2TORS.exceptionalFibres.{p2m_u_0} G inst inst_1 inst_2)))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Fintype.card.{p2m_u_0} G inst_2)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := @_root_.Couret.STROBO2TORS.p2m_local_exceptionalFibres_weighted_card

