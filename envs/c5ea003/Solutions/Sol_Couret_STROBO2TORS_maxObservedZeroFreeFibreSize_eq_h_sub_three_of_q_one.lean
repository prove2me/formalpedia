-- Prove2me | solution 1 for Couret.STROBO2TORS.maxObservedZeroFreeFibreSize_eq_h_sub_three_of_q_one
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:22.3111+00:00
-- url     : https://prove2.me/submissions/3daa9f02-65ef-4fd2-a172-6ebc426637ec

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
import Theorems.Thm_Couret_STROBO2TORS_maxObservedZeroFreeFibreSize_pos_of_four
import Theorems.Thm_Couret_STROBO2TORS_mem_threeTorsion
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibres_zeroFree_size
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_eq_empty_of_no_three_torsion
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_eq_union
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























/-- If the doubling image has just one class, every group element is
two-torsion. For |G|>=4 the exact largest observed zero-free fibre has
h-3 supports: three translations of any triple hit the origin. -/
theorem p2m_local_maxObservedZeroFreeFibreSize_eq_h_sub_three_of_q_one
    (hq : (doublingImages : Finset G).card = 1)
    (hn : 4 ≤ Fintype.card G) :
    maxObservedZeroFreeFibreSize (G := G) =
      (twoTorsion : Finset G).card - 3 := by
  have hCount : Fintype.card G = (twoTorsion : Finset G).card := by
    simpa [hq] using (group_card_eq_h_mul_doublingImages (G := G))
  have hFull : (twoTorsion : Finset G) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hCount]
  have hThree : (threeTorsion : Finset G) = {0} := by
    ext v
    rw [mem_threeTorsion]
    simp only [Finset.mem_singleton]
    constructor
    · intro hv
      have hvTwo : v + v = 0 :=
        (mem_twoTorsion v).mp (by rw [hFull]; simp)
      rw [hvTwo] at hv
      simpa using hv
    · intro hv
      subst v
      simp
  have ht : (threeTorsion : Finset G).card = 1 := by
    rw [hThree]
    simp
  have hEmpty : (zeroFreeExceptionalFibres : Finset (Finset (Finset G))) = ∅ :=
    zeroFreeExceptionalFibres_eq_empty_of_no_three_torsion ht
  have hEach : ∀ F : Finset (Finset G),
      F ∈ (zeroFreeFullFibres : Finset (Finset (Finset G))) →
        F.card = (twoTorsion : Finset G).card - 3 := by
    intro F hF
    rw [zeroFreeFullFibres_eq_union, hEmpty] at hF
    have hOrd : F ∈ (zeroFreeOrdinaryFibres : Finset (Finset (Finset G))) := by
      simpa using hF
    obtain ⟨K, hK, hFK⟩ := Finset.mem_image.mp hOrd
    have hOrigOrd : K ∈ (ordinaryFibres : Finset (Finset (Finset G))) :=
      (Finset.mem_filter.mp hK).1
    obtain ⟨S, hS3, _, hSize⟩ := ordinaryFibres_zeroFree_size K hOrigOrd
    have hInter : (S ∩ (twoTorsion : Finset G)).card = 3 := by
      simpa [hFull] using hS3
    rw [← hFK, hSize, hInter]
  have hExists : (zeroFreeFullFibres : Finset (Finset (Finset G))).Nonempty := by
    by_contra hNo
    have hEmptyFibres : (zeroFreeFullFibres : Finset (Finset (Finset G))) = ∅ := by
      ext F
      constructor
      · intro hF
        exact False.elim (hNo ⟨F, hF⟩)
      · intro hF
        simp at hF
    have hMzero : maxObservedZeroFreeFibreSize (G := G) = 0 := by
      simp [maxObservedZeroFreeFibreSize, hEmptyFibres]
    have hPositive := maxObservedZeroFreeFibreSize_pos_of_four (G := G) hn
    omega
  obtain ⟨F, hF⟩ := hExists
  exact maxObservedZeroFreeFibreSize_eq_of_attained (G := G)
    ((twoTorsion : Finset G).card - 3)
    (by intro K hK; exact le_of_eq (hEach K hK))
    ⟨F, hF, hEach F hF⟩














end Couret.STROBO2TORS







universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.doublingImages.{p2m_u_0} G inst inst_1 inst_2))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@Fintype.card.{p2m_u_0} G inst_2) →
      @Eq.{1} Nat (@Couret.STROBO2TORS.maxObservedZeroFreeFibreSize.{p2m_u_0} G inst inst_1 inst_2)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) := @_root_.Couret.STROBO2TORS.p2m_local_maxObservedZeroFreeFibreSize_eq_h_sub_three_of_q_one

