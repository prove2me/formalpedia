-- Prove2me | solution 1 for Couret.STROBO2TORS.maxObservedZeroFreeFibreSize_complete
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:53:01.051931+00:00
-- url     : https://prove2.me/submissions/a1b891fc-4343-4705-a02f-ed8343bb09c7

import Aesop
import Definitions.Def_Couret_Strobo2TorsSharpMaximum_bfb30eac9be9
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_maxObservedZeroFreeFibreSize_eq_h_sub_three_of_q_one
import Theorems.Thm_Couret_STROBO2TORS_maxObservedZeroFreeFibreSize_eq_one_of_card_four
import Theorems.Thm_Couret_STROBO2TORS_maxObservedZeroFreeFibreSize_eq_one_of_trivial_two_torsion
import Theorems.Thm_Couret_STROBO2TORS_maxObservedZeroFreeFibreSize_eq_zero_of_card_lt_four
import Theorems.Thm_Couret_STROBO2TORS_mem_threeTorsion
import Theorems.Thm_Couret_STROBO2TORS_outsideTwoTorsion_card_ge_three_of_large_quotient
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_card_le_h_of_no_three_torsion
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_card_le_reduced_of_q_le_three
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_card_le_two_torsion
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_reduced_size_exists
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_size_h_exists_of_no_three_torsion
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_top_size_nonempty_iff
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]



/-- A finite upper bound plus a witness of equality determine the exact
maximum. This lemma does not assume the collection is nonempty. -/
theorem maxObservedZeroFreeFibreSize_eq_of_attained (k : ℕ)
    (hBound : ∀ F : Finset (Finset G),
      F ∈ (zeroFreeFullFibres : Finset (Finset (Finset G))) → F.card ≤ k)
    (hWitness : ∃ F : Finset (Finset G),
      F ∈ (zeroFreeFullFibres : Finset (Finset (Finset G))) ∧ F.card = k) :
    maxObservedZeroFreeFibreSize (G := G) = k := by
  apply Nat.le_antisymm
  · unfold maxObservedZeroFreeFibreSize
    apply Finset.sup_le
    intro F hF
    exact hBound F hF
  · obtain ⟨F, hF, hCard⟩ := hWitness
    have hLe : F.card ≤ maxObservedZeroFreeFibreSize (G := G) := by
      unfold maxObservedZeroFreeFibreSize
      exact Finset.le_sup hF
    simpa only [hCard] using hLe





/-- Exact maximum in the reduced exceptional regime, including q = 3
and all cases with q <= 3, h > 1 and nontrivial three-torsion. -/
theorem maxObservedZeroFreeFibreSize_eq_reduced
    (hq : (doublingImages : Finset G).card ≤ 3)
    (hh : 1 < (twoTorsion : Finset G).card)
    (ht : 1 < (threeTorsion : Finset G).card) :
    maxObservedZeroFreeFibreSize (G := G) =
      2 * (twoTorsion : Finset G).card - 2 := by
  apply maxObservedZeroFreeFibreSize_eq_of_attained (G := G)
  · intro F hF
    exact zeroFreeFullFibres_card_le_reduced_of_q_le_three hq (by omega) F hF
  · exact zeroFreeFullFibres_reduced_size_exists hh ht

/-- Exact maximum in the full exceptional regime q > 3, h > 1, t > 1. -/
theorem maxObservedZeroFreeFibreSize_eq_full
    (hq : 3 < (doublingImages : Finset G).card)
    (hh : 1 < (twoTorsion : Finset G).card)
    (ht : 1 < (threeTorsion : Finset G).card) :
    maxObservedZeroFreeFibreSize (G := G) =
      2 * (twoTorsion : Finset G).card := by
  apply maxObservedZeroFreeFibreSize_eq_of_attained (G := G)
  · intro F hF
    exact zeroFreeFullFibres_card_le_two_torsion F hF
  · obtain ⟨F, hF⟩ :=
      (zeroFreeFullFibres_top_size_nonempty_iff (G := G)).mpr ⟨hq, hh, ht⟩
    exact ⟨F, (Finset.mem_filter.mp hF).1, (Finset.mem_filter.mp hF).2⟩











/-- A sharp result for all no-three-torsion groups with at least three
elements outside G[2]. This covers all nondegenerate large quotients. -/
theorem maxObservedZeroFreeFibreSize_eq_h_of_no_three_torsion
    (ht : (threeTorsion : Finset G).card = 1)
    (hOutside : 3 ≤
      ((Finset.univ : Finset G) \ (twoTorsion : Finset G)).card) :
    maxObservedZeroFreeFibreSize (G := G) =
      (twoTorsion : Finset G).card := by
  apply maxObservedZeroFreeFibreSize_eq_of_attained (G := G)
  · intro F hF
    exact zeroFreeFullFibres_card_le_h_of_no_three_torsion ht F hF
  · exact zeroFreeFullFibres_size_h_exists_of_no_three_torsion ht hOutside













/-- The remaining large no-three-torsion case has exact maximum h.
The inequalities exclude the sole small quotient exception at |G|=4. -/
theorem maxObservedZeroFreeFibreSize_eq_h_of_no_three_torsion_large
    (ht : (threeTorsion : Finset G).card = 1)
    (hh : 1 < (twoTorsion : Finset G).card)
    (hq : 1 < (doublingImages : Finset G).card)
    (hn : 4 < Fintype.card G) :
    maxObservedZeroFreeFibreSize (G := G) =
      (twoTorsion : Finset G).card := by
  exact maxObservedZeroFreeFibreSize_eq_h_of_no_three_torsion
    ht (outsideTwoTorsion_card_ge_three_of_large_quotient hh hq hn)

/-- Exhaustive sharp maximum of observed zero-free ordered-square fibres.
The branches are ordered to avoid overlap at small group orders. -/
theorem p2m_local_maxObservedZeroFreeFibreSize_complete :
    maxObservedZeroFreeFibreSize (G := G) =
      if Fintype.card G < 4 then 0
      else if (twoTorsion : Finset G).card = 1 then 1
      else if (doublingImages : Finset G).card = 1 then
        (twoTorsion : Finset G).card - 3
      else if Fintype.card G = 4 then 1
      else if (threeTorsion : Finset G).card = 1 then
        (twoTorsion : Finset G).card
      else if (doublingImages : Finset G).card ≤ 3 then
        2 * (twoTorsion : Finset G).card - 2
      else 2 * (twoTorsion : Finset G).card := by
  by_cases hnSmall : Fintype.card G < 4
  · simp only [if_pos hnSmall]
    exact maxObservedZeroFreeFibreSize_eq_zero_of_card_lt_four hnSmall
  · have hnFour : 4 ≤ Fintype.card G := by omega
    by_cases hhOne : (twoTorsion : Finset G).card = 1
    · simp only [if_neg hnSmall, if_pos hhOne]
      exact maxObservedZeroFreeFibreSize_eq_one_of_trivial_two_torsion hhOne hnFour
    · have hhBig : 1 < (twoTorsion : Finset G).card := by
        have hhPos := twoTorsion_card_pos (G := G)
        omega
      by_cases hqOne : (doublingImages : Finset G).card = 1
      · simp only [if_neg hnSmall, if_neg hhOne, if_pos hqOne]
        exact maxObservedZeroFreeFibreSize_eq_h_sub_three_of_q_one hqOne hnFour
      · have hqPos : 0 < (doublingImages : Finset G).card := by
          apply Finset.card_pos.mpr
          exact ⟨0, Finset.mem_image.mpr
            ⟨0, Finset.mem_univ _, by simp [doublingImages]⟩⟩
        have hqBig : 1 < (doublingImages : Finset G).card := by omega
        by_cases hnEqFour : Fintype.card G = 4
        · simp only [if_neg hnSmall, if_neg hhOne,
            if_neg hqOne, if_pos hnEqFour]
          exact maxObservedZeroFreeFibreSize_eq_one_of_card_four hnEqFour
        · have hnLarge : 4 < Fintype.card G := by omega
          by_cases htOne : (threeTorsion : Finset G).card = 1
          · simp only [if_neg hnSmall, if_neg hhOne,
              if_neg hqOne, if_neg hnEqFour, if_pos htOne]
            exact maxObservedZeroFreeFibreSize_eq_h_of_no_three_torsion_large
              htOne hhBig hqBig hnLarge
          · have htPos : 0 < (threeTorsion : Finset G).card := by
              apply Finset.card_pos.mpr
              exact ⟨0, (mem_threeTorsion 0).mpr (by simp)⟩
            have htBig : 1 < (threeTorsion : Finset G).card := by omega
            by_cases hqSmall : (doublingImages : Finset G).card ≤ 3
            · simp only [if_neg hnSmall, if_neg hhOne,
                if_neg hqOne, if_neg hnEqFour, if_neg htOne,
                if_pos hqSmall]
              exact maxObservedZeroFreeFibreSize_eq_reduced hqSmall hhBig htBig
            · have hqLarge : 3 < (doublingImages : Finset G).card := by omega
              simp only [if_neg hnSmall, if_neg hhOne,
                if_neg hqOne, if_neg hnEqFour, if_neg htOne,
                if_neg hqSmall]
              exact maxObservedZeroFreeFibreSize_eq_full hqLarge hhBig htBig


end Couret.STROBO2TORS







universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat (@Couret.STROBO2TORS.maxObservedZeroFreeFibreSize.{p2m_u_0} G inst inst_1 inst_2)
    (@ite.{1} Nat
      (@LT.lt.{0} Nat instLTNat (@Fintype.card.{p2m_u_0} G inst_2)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (Nat.decLt (@Fintype.card.{p2m_u_0} G inst_2) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@ite.{1} Nat
        (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (instDecidableEqNat (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@ite.{1} Nat
          (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.doublingImages.{p2m_u_0} G inst inst_1 inst_2))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (instDecidableEqNat
            (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.doublingImages.{p2m_u_0} G inst inst_1 inst_2))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@ite.{1} Nat
            (@Eq.{1} Nat (@Fintype.card.{p2m_u_0} G inst_2)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (instDecidableEqNat (@Fintype.card.{p2m_u_0} G inst_2)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@ite.{1} Nat
              (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (instDecidableEqNat
                (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
              (@ite.{1} Nat
                (@LE.le.{0} Nat instLENat
                  (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.doublingImages.{p2m_u_0} G inst inst_1 inst_2))
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (Nat.decLe
                  (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.doublingImages.{p2m_u_0} G inst inst_1 inst_2))
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))))))))) := @_root_.Couret.STROBO2TORS.p2m_local_maxObservedZeroFreeFibreSize_complete

