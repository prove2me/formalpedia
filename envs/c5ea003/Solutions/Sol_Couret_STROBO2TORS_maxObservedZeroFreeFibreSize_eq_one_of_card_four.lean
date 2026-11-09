-- Prove2me | solution 1 for Couret.STROBO2TORS.maxObservedZeroFreeFibreSize_eq_one_of_card_four
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:38:46.5332+00:00
-- url     : https://prove2.me/submissions/39a21310-8c46-4843-9e8e-04713d7d8793

import Aesop
import Definitions.Def_Couret_Strobo2TorsSharpMaximum_bfb30eac9be9
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_maxObservedZeroFreeFibreSize_pos_of_four
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]































/-- At group order four there is exactly one available zero-free support,
so the observed maximum is exactly one. -/
theorem p2m_local_maxObservedZeroFreeFibreSize_eq_one_of_card_four
    (hn : Fintype.card G = 4) :
    maxObservedZeroFreeFibreSize (G := G) = 1 := by
  have hpos : 0 < maxObservedZeroFreeFibreSize (G := G) :=
    maxObservedZeroFreeFibreSize_pos_of_four (G := G) (by omega)
  have hBound : maxObservedZeroFreeFibreSize (G := G) ≤ 1 := by
    unfold maxObservedZeroFreeFibreSize
    apply Finset.sup_le
    intro F hF
    have hUnique : ∀ S : Finset G, S.card = 3 → (0 : G) ∉ S →
        S = (Finset.univ : Finset G).erase 0 := by
      intro S hs hzero
      have hSub : S ⊆ (Finset.univ : Finset G).erase 0 := by
        intro x hx
        exact Finset.mem_erase.mpr
          ⟨(fun h => hzero (h ▸ hx)), Finset.mem_univ x⟩
      have hc : ((Finset.univ : Finset G).erase (0 : G)).card = 3 := by
        simp [hn]
      exact Finset.eq_of_subset_of_card_le hSub (by omega)
    have hFsub : F ⊆ ({(Finset.univ : Finset G).erase 0} : Finset (Finset G)) := by
      intro S hS
      have hc : S.card = 3 ∧ (0 : G) ∉ S := by
        change F ∈ (nonemptyFullFibres : Finset (Finset (Finset G))).image withoutZero at hF
        obtain ⟨K, hK, hKF⟩ := Finset.mem_image.mp hF
        rw [← hKF] at hS
        obtain ⟨hSK, hZero⟩ := Finset.mem_filter.mp hS
        have hAll : K ∈ (allSquareFibres : Finset (Finset (Finset G))) :=
          (Finset.mem_filter.mp hK).1
        obtain ⟨T, _, hTK⟩ := Finset.mem_image.mp hAll
        have hSsq : S ∈ squareFibre T := by
          rw [hTK]
          exact hSK
        exact ⟨((mem_squareFibre T S).mp hSsq).1, hZero⟩
      simp [hUnique S hc.1 hc.2]
    calc
      F.card ≤ ({(Finset.univ : Finset G).erase 0} :
          Finset (Finset G)).card := Finset.card_le_card hFsub
      _ = 1 := by simp
  omega










end Couret.STROBO2TORS







universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat (@Fintype.card.{p2m_u_0} G inst_2) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
    @Eq.{1} Nat (@Couret.STROBO2TORS.maxObservedZeroFreeFibreSize.{p2m_u_0} G inst inst_1 inst_2)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) := @_root_.Couret.STROBO2TORS.p2m_local_maxObservedZeroFreeFibreSize_eq_one_of_card_four

