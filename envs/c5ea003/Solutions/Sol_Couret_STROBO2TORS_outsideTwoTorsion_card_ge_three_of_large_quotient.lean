-- Prove2me | solution 1 for Couret.STROBO2TORS.outsideTwoTorsion_card_ge_three_of_large_quotient
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:38:49.521978+00:00
-- url     : https://prove2.me/submissions/2f957efa-acb8-404d-8836-f1bb6dbcd78d

import Aesop
import Definitions.Def_Couret_Strobo2TorsSharpMaximum_bfb30eac9be9
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_group_card_eq_h_mul_doublingImages
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]



































/-- In a group with nontrivial two-torsion and doubling quotient,
order greater than four guarantees at least three elements outside G[2].
This is a purely numerical consequence of |G|=h*q. -/
theorem p2m_local_outsideTwoTorsion_card_ge_three_of_large_quotient
    (hh : 1 < (twoTorsion : Finset G).card)
    (hq : 1 < (doublingImages : Finset G).card)
    (hn : 4 < Fintype.card G) :
    3 ≤ ((Finset.univ : Finset G) \ (twoTorsion : Finset G)).card := by
  have hOutside :
      ((Finset.univ : Finset G) \ (twoTorsion : Finset G)).card =
        Fintype.card G - (twoTorsion : Finset G).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  have hqTwo : 2 ≤ (doublingImages : Finset G).card := by omega
  have hTwice : 2 * (twoTorsion : Finset G).card ≤ Fintype.card G := by
    calc
      2 * (twoTorsion : Finset G).card =
          (twoTorsion : Finset G).card * 2 := Nat.mul_comm _ _
      _ ≤ (twoTorsion : Finset G).card *
          (doublingImages : Finset G).card :=
            Nat.mul_le_mul_left _ hqTwo
      _ = Fintype.card G :=
            (group_card_eq_h_mul_doublingImages (G := G)).symm
  rw [hOutside]
  omega






end Couret.STROBO2TORS







universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)) →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.doublingImages.{p2m_u_0} G inst inst_1 inst_2)) →
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@Fintype.card.{p2m_u_0} G inst_2) →
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@Finset.card.{p2m_u_0} G
            (@SDiff.sdiff.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instSDiff.{p2m_u_0} G inst_1)
              (@Finset.univ.{p2m_u_0} G inst_2) (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))) := @_root_.Couret.STROBO2TORS.p2m_local_outsideTwoTorsion_card_ge_three_of_large_quotient

