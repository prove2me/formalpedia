-- Prove2me | solution 1 for Couret.STROBO2TORS.nontranslationPairs_card_of_h_two
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:53:13.111196+00:00
-- url     : https://prove2.me/submissions/a0810ba5-eefb-4449-847e-dfb98f0bf825

import Aesop
import Definitions.Def_Couret_Strobo2TorsPairCount_5c76f0dc12bb
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_doublingImages_card_division
import Theorems.Thm_Couret_STROBO2TORS_group_card_eq_h_mul_doublingImages
import Theorems.Thm_Couret_STROBO2TORS_orderedNontranslationPairs_card_eq_twice
import Theorems.Thm_Couret_STROBO2TORS_pairParameters_card
import Theorems.Thm_Couret_STROBO2TORS_pairRealization_image
import Theorems.Thm_Couret_STROBO2TORS_pairRealization_injective_on
import Theorems.Thm_Couret_STROBO2TORS_threeSignPairs_card_division
import Theorems.Thm_Couret_STROBO2TORS_threeTorsion_nonzero_card_eq_two_pairs
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
namespace Couret.STROBO2TORS
variable {G : Type*} [AddCommGroup G] [DecidableEq G]







section Finite
variable [Fintype G]
































attribute [local instance] Classical.propDecidable







theorem orderedNontranslationPairs_card :
    (orderedNontranslationPairs : Finset (Finset G × Finset G)).card =
      ((twoTorsion : Finset G).card-1) * ((threeTorsion : Finset G).card-1) *
        (Fintype.card G * (twoTorsion : Finset G).card - 6 * (twoTorsion : Finset G).card + 1) := by
  rw [← pairRealization_image,Finset.card_image_iff.mpr pairRealization_injective_on,pairParameters_card]











/-- Universal count of unordered nontranslated zero-free triple-support
collisions. q=|G|/h is implemented as the certified doubling-image count. -/
theorem nontranslationPairs_card_product :
    (nontranslationPairs : Finset (Finset (Finset G))).card =
      ((twoTorsion : Finset G).card-1) * (threeSignPairs : Finset (Finset G)).card *
        ((doublingImages : Finset G).card * (twoTorsion : Finset G).card ^ 2 -
          6 * (twoTorsion : Finset G).card + 1) := by
  apply Nat.eq_of_mul_eq_mul_left (n:=2) (by decide)
  rw [← orderedNontranslationPairs_card_eq_twice,orderedNontranslationPairs_card,
    threeTorsion_nonzero_card_eq_two_pairs,group_card_eq_h_mul_doublingImages]
  have he : (twoTorsion : Finset G).card * (doublingImages : Finset G).card *
      (twoTorsion : Finset G).card = (doublingImages : Finset G).card * (twoTorsion : Finset G).card^2 := by ring
  rw [he]
  ring

theorem nontranslationPairs_card_numeric :
    (nontranslationPairs : Finset (Finset (Finset G))).card =
      ((twoTorsion : Finset G).card-1) * (((threeTorsion : Finset G).card-1)/2) *
        ((Fintype.card G / (twoTorsion : Finset G).card) * (twoTorsion : Finset G).card ^ 2 -
          6 * (twoTorsion : Finset G).card + 1) := by
  rw [nontranslationPairs_card_product,threeSignPairs_card_division,doublingImages_card_division]





theorem p2m_local_nontranslationPairs_card_of_h_two (hh : (twoTorsion : Finset G).card=2) :
    (nontranslationPairs : Finset (Finset (Finset G))).card =
      (((threeTorsion : Finset G).card-1)/2) *
        (4 * (Fintype.card G / 2) - 12 + 1) := by
  rw [nontranslationPairs_card_numeric,hh]
  simp [Nat.mul_comm]

end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
    @Eq.{1} Nat
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Couret.STROBO2TORS.nontranslationPairs.{p2m_u_0} G inst inst_1 inst_2))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) (@Fintype.card.{p2m_u_0} G inst_2)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := @_root_.Couret.STROBO2TORS.p2m_local_nontranslationPairs_card_of_h_two

