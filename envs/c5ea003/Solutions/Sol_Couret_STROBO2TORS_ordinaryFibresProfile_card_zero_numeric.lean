-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinaryFibresProfile_card_zero_numeric
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:44:31.846296+00:00
-- url     : https://prove2.me/submissions/7a656aff-0a98-4661-a3c4-9a7444c01bb4

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupportsProfile_one_card
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupportsProfile_two_card
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupports_card
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupports_card_profile_partition
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_card_sub_div
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]









/-- The arithmetic subtraction in the closed form uses truncated natural
subtraction, hence works even for groups where no exceptional support exists. -/
private theorem sub_double_mul (n h a b : ℕ) :
    (n - 2 * h) * a * b =
      n * a * b - (h * a * b + h * a * b) := by
  calc
    (n - 2 * h) * a * b =
        (n - 2 * h) * (a * b) := by rw [mul_assoc]
    _ = n * (a * b) - (2 * h) * (a * b) :=
      Nat.sub_mul n (2 * h) (a * b)
    _ = n * a * b - (h * a * b + h * a * b) := by
      simp only [mul_assoc, two_mul, add_mul]

/-- Closed count X0 of exceptional SUPPORTS avoiding G[2]. The derivation
uses the proved X1=X2 bijection and the disjoint profile partition. -/
theorem exceptionalSupportsProfile_zero_card :
    (exceptionalSupportsProfile (G := G) 0).card =
      (Fintype.card G - 2 * (twoTorsion : Finset G).card) *
        ((twoTorsion : Finset G).card - 1) *
        ((threeTorsion : Finset G).card - 1) := by
  have hBal := exceptionalSupports_card_profile_partition (G := G)
  rw [exceptionalSupports_card, exceptionalSupportsProfile_one_card,
    exceptionalSupportsProfile_two_card] at hBal
  have hArith := sub_double_mul (Fintype.card G)
    (twoTorsion : Finset G).card
    ((twoTorsion : Finset G).card - 1)
    ((threeTorsion : Finset G).card - 1)
  omega

/-- Closed numerical count of ordinary full square fibres with no points
in G[2]. This concerns complete fibres; zero-free size aggregation is
a distinct subsequent step. -/
theorem p2m_local_ordinaryFibresProfile_card_zero_numeric :
    (ordinaryFibresProfile (G := G) 0).card =
      (((twoTorsion : Finset G).card.choose 0) *
          ((Fintype.card G - (twoTorsion : Finset G).card).choose 3) -
        ((Fintype.card G - 2 * (twoTorsion : Finset G).card) *
          ((twoTorsion : Finset G).card - 1) *
          ((threeTorsion : Finset G).card - 1))) /
        (twoTorsion : Finset G).card := by
  rw [ordinaryFibresProfile_card_sub_div 0 (by omega),
    exceptionalSupportsProfile_zero_card]

end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Couret.STROBO2TORS.ordinaryFibresProfile.{p2m_u_0} G inst inst_1 inst_2
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (Nat.choose (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Nat.choose
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Fintype.card.{p2m_u_0} G inst_2)
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Fintype.card.{p2m_u_0} G inst_2)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))) := @_root_.Couret.STROBO2TORS.p2m_local_ordinaryFibresProfile_card_zero_numeric

