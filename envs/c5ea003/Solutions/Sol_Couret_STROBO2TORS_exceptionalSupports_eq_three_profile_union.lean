-- Prove2me | solution 1 for Couret.STROBO2TORS.exceptionalSupports_eq_three_profile_union
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:16:38.053866+00:00
-- url     : https://prove2.me/submissions/8652aeb8-4891-4b25-91fa-d9c7ecd281ca

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupportsProfile_three_eq_empty
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports_card
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupportsProfile
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

/-- A profile stratum is an actual exceptional support, with the indicated
number of members in the two-torsion subgroup. -/
theorem mem_exceptionalSupportsProfile_iff (S : Finset G) (j : ℕ) :
    S ∈ exceptionalSupportsProfile j ↔
      S ∈ (exceptionalSupports : Finset (Finset G)) ∧
        (S ∩ (twoTorsion : Finset G)).card = j := by
  constructor
  · intro h
    obtain ⟨hProfile, hSize⟩ := Finset.mem_filter.mp h
    obtain ⟨hThree, hj⟩ := (mem_tripleSupportsProfile S j).mp hProfile
    exact ⟨(mem_exceptionalSupports_card S).mpr ⟨hThree, hSize⟩, hj⟩
  · rintro ⟨hExc, hj⟩
    obtain ⟨hThree, hSize⟩ := (mem_exceptionalSupports_card S).mp hExc
    exact Finset.mem_filter.mpr
      ⟨(mem_tripleSupportsProfile S j).mpr ⟨hThree, hj⟩, hSize⟩



/-- Exceptional supports have only the profiles j=0,1,2.
The case j=3 was already ruled out by the structural classification. -/
theorem p2m_local_exceptionalSupports_eq_three_profile_union :
    (exceptionalSupports : Finset (Finset G)) =
      exceptionalSupportsProfile 0 ∪
        (exceptionalSupportsProfile 1 ∪ exceptionalSupportsProfile 2) := by
  ext S
  constructor
  · intro hExc
    have hThree := ((mem_exceptionalSupports_card S).mp hExc).1
    have hBound : (S ∩ (twoTorsion : Finset G)).card ≤ 3 := by
      have hs : (S ∩ (twoTorsion : Finset G)) ⊆ S := Finset.inter_subset_left
      have hc := Finset.card_le_card hs
      omega
    have hc : (S ∩ (twoTorsion : Finset G)).card = 0 ∨
        (S ∩ (twoTorsion : Finset G)).card = 1 ∨
        (S ∩ (twoTorsion : Finset G)).card = 2 ∨
        (S ∩ (twoTorsion : Finset G)).card = 3 := by omega
    rcases hc with h0 | h1 | h2 | h3
    · exact Finset.mem_union.mpr (Or.inl
        ((mem_exceptionalSupportsProfile_iff S 0).mpr ⟨hExc, h0⟩))
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_union.mpr (Or.inl
          ((mem_exceptionalSupportsProfile_iff S 1).mpr ⟨hExc, h1⟩))))
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_union.mpr (Or.inr
          ((mem_exceptionalSupportsProfile_iff S 2).mpr ⟨hExc, h2⟩))))
    · have hf : S ∈ (exceptionalSupportsProfile (G := G) 3) :=
        (mem_exceptionalSupportsProfile_iff S 3).mpr ⟨hExc, h3⟩
      rw [exceptionalSupportsProfile_three_eq_empty] at hf
      simp at hf
  · intro h
    rcases Finset.mem_union.mp h with h0 | h12
    · exact ((mem_exceptionalSupportsProfile_iff S 0).mp h0).1
    · rcases Finset.mem_union.mp h12 with h1 | h2
      · exact ((mem_exceptionalSupportsProfile_iff S 1).mp h1).1
      · exact ((mem_exceptionalSupportsProfile_iff S 2).mp h2).1









end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
    (@Couret.STROBO2TORS.exceptionalSupports.{p2m_u_0} G inst inst_1 inst_2)
    (@Union.union.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Finset.instUnion.{p2m_u_0} (Finset.{p2m_u_0} G) fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b)
      (@Couret.STROBO2TORS.exceptionalSupportsProfile.{p2m_u_0} G inst inst_1 inst_2
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Union.union.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Finset.instUnion.{p2m_u_0} (Finset.{p2m_u_0} G) fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b)
        (@Couret.STROBO2TORS.exceptionalSupportsProfile.{p2m_u_0} G inst inst_1 inst_2
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Couret.STROBO2TORS.exceptionalSupportsProfile.{p2m_u_0} G inst inst_1 inst_2
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) := @_root_.Couret.STROBO2TORS.p2m_local_exceptionalSupports_eq_three_profile_union

