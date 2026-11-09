-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeExceptionalFibres_full_nonempty_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:21:46.932664+00:00
-- url     : https://prove2.me/submissions/a9aeb118-05e6-41ff-82a1-5876598533be

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_threeTorsion_nonzero_card_eq_two_pairs
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_full_card
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]











































































theorem p2m_local_zeroFreeExceptionalFibres_full_nonempty_iff :
    ((zeroFreeExceptionalFibres : Finset (Finset (Finset G))).filter
      (fun F => F.card = 2 * (twoTorsion : Finset G).card)).Nonempty ↔
      3 < (doublingImages : Finset G).card ∧ 1 < (twoTorsion : Finset G).card ∧
        1 < (threeTorsion : Finset G).card := by
  rw [← Finset.card_pos, zeroFreeExceptionalFibres_full_card]
  have ht := threeTorsion_nonzero_card_eq_two_pairs (G := G)
  constructor
  · intro hp
    have hpqh := Nat.pos_of_mul_pos_right hp
    have hpq := Nat.pos_of_mul_pos_right hpqh
    have hph := Nat.pos_of_mul_pos_left hpqh
    have hpr := Nat.pos_of_mul_pos_left hp
    omega
  · rintro ⟨hq, hh, hk⟩
    have hpq : 0 < (doublingImages : Finset G).card - 3 := by omega
    have hph : 0 < (twoTorsion : Finset G).card - 1 := by omega
    have hpr : 0 < (threeSignPairs : Finset (Finset G)).card := by omega
    exact Nat.mul_pos (Nat.mul_pos hpq hph) hpr



end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  Iff
    (@Finset.Nonempty.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Finset.filter.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (fun F =>
          @Eq.{1} Nat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) F)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))))
        (fun a =>
          instDecidableEqNat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) a)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))))
        (@Couret.STROBO2TORS.zeroFreeExceptionalFibres.{p2m_u_0} G inst inst_1 inst_2)))
    (And
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.doublingImages.{p2m_u_0} G inst inst_1 inst_2)))
      (And
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeExceptionalFibres_full_nonempty_iff

