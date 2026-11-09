-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeExceptionalFibres_full_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:18:20.178142+00:00
-- url     : https://prove2.me/submissions/7ee58400-dd4a-4114-8d92-5de171e1b364

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_card_product
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_filter_full_eq
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_preimage
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_withoutZero_card_ge_two
import Theorems.Thm_Couret_STROBO2TORS_threeTorsion_nonzero_card_eq_two_pairs
import Theorems.Thm_Couret_STROBO2TORS_zeroHitExceptionalFibres_weighted_card
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]



































theorem zeroHitExceptionalFibres_subset :
    (zeroHitExceptionalFibres : Finset (Finset (Finset G))) ⊆ exceptionalFibres := by
  intro F hF
  obtain ⟨S, hS, hsF⟩ := Finset.mem_image.mp hF
  exact Finset.mem_image.mpr ⟨S, (Finset.mem_filter.mp hS).1, hsF⟩







theorem zeroHitExceptionalFibres_card :
    (zeroHitExceptionalFibres : Finset (Finset (Finset G))).card =
      3 * ((twoTorsion : Finset G).card - 1) * (threeSignPairs : Finset (Finset G)).card := by
  apply Nat.eq_of_mul_eq_mul_left (n := 2) (by decide)
  rw [zeroHitExceptionalFibres_weighted_card, threeTorsion_nonzero_card_eq_two_pairs]
  ac_rfl

theorem zeroMissingExceptionalFibres_card :
    (zeroMissingExceptionalFibres : Finset (Finset (Finset G))).card =
      ((doublingImages : Finset G).card - 3) * ((twoTorsion : Finset G).card - 1) *
        (threeSignPairs : Finset (Finset G)).card := by
  unfold zeroMissingExceptionalFibres
  rw [Finset.card_sdiff_of_subset zeroHitExceptionalFibres_subset,
    exceptionalFibres_card_product, zeroHitExceptionalFibres_card]
  simp only [Nat.sub_mul, Nat.mul_assoc]











theorem exceptionalFibres_squareFibre_member (F : Finset (Finset G))
    (hF : F ∈ (exceptionalFibres : Finset (Finset (Finset G))))
    (S : Finset G) (hS : S ∈ F) : squareFibre S = F := by
  have hp : S ∈ exceptionalSupports.filter (fun T : Finset G => squareFibre T = F) := by
    rw [exceptionalFibres_preimage F hF]
    exact hS
  exact (Finset.mem_filter.mp hp).2

/-- Removing zero neither empties nor identifies two exceptional fibres. -/
theorem withoutZero_injective_on_exceptionalFibres :
    Set.InjOn (withoutZero : Finset (Finset G) → Finset (Finset G))
      (exceptionalFibres : Finset (Finset (Finset G))) := by
  intro F hF K hK heq
  have hc := exceptionalFibres_withoutZero_card_ge_two F hF
  obtain ⟨S, hS⟩ := Finset.card_pos.mp (by omega : 0 < (withoutZero F).card)
  have hSK : S ∈ withoutZero K := by rw [← heq]; exact hS
  have hsF := exceptionalFibres_squareFibre_member F hF S (Finset.mem_filter.mp hS).1
  have hsK := exceptionalFibres_squareFibre_member K hK S (Finset.mem_filter.mp hSK).1
  exact hsF.symm.trans hsK









theorem zeroFreeExceptionalFibres_filter_card (k : ℕ) :
    ((zeroFreeExceptionalFibres : Finset (Finset (Finset G))).filter (fun F => F.card = k)).card =
      ((exceptionalFibres : Finset (Finset (Finset G))).filter
        (fun F => (withoutZero F).card = k)).card := by
  unfold zeroFreeExceptionalFibres
  rw [Finset.filter_image]
  apply Finset.card_image_iff.mpr
  intro F hF K hK heq
  exact withoutZero_injective_on_exceptionalFibres
    (Finset.mem_filter.mp hF).1 (Finset.mem_filter.mp hK).1 heq



theorem p2m_local_zeroFreeExceptionalFibres_full_card :
    ((zeroFreeExceptionalFibres : Finset (Finset (Finset G))).filter
      (fun F => F.card = 2 * (twoTorsion : Finset G).card)).card =
      ((doublingImages : Finset G).card - 3) * ((twoTorsion : Finset G).card - 1) *
        (threeSignPairs : Finset (Finset G)).card := by
  rw [zeroFreeExceptionalFibres_filter_card, exceptionalFibres_filter_full_eq,
    zeroMissingExceptionalFibres_card]





end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
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
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.doublingImages.{p2m_u_0} G inst inst_1 inst_2))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.threeSignPairs.{p2m_u_0} G inst inst_1 inst_2))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeExceptionalFibres_full_card

