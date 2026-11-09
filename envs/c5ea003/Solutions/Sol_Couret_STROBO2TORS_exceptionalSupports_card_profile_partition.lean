-- Prove2me | solution 1 for Couret.STROBO2TORS.exceptionalSupports_card_profile_partition
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:26:07.330563+00:00
-- url     : https://prove2.me/submissions/af1190ba-4d24-4476-972b-4a11d925a317

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupports_eq_three_profile_union
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

theorem exceptionalSupportsProfile_pair_disjoint (j k : ℕ) (hne : j ≠ k) :
    Disjoint (exceptionalSupportsProfile (G := G) j)
      (exceptionalSupportsProfile (G := G) k) := by
  apply Finset.disjoint_left.mpr
  intro S hj hk
  have hsj := ((mem_exceptionalSupportsProfile_iff S j).mp hj).2
  have hsk := ((mem_exceptionalSupportsProfile_iff S k).mp hk).2
  exact hne (hsj.symm.trans hsk)



/-- Disjoint partition at the SUPPORT level, not the fibre level. -/
theorem p2m_local_exceptionalSupports_card_profile_partition :
    (exceptionalSupports : Finset (Finset G)).card =
      (exceptionalSupportsProfile (G := G) 0).card +
      (exceptionalSupportsProfile (G := G) 1).card +
      (exceptionalSupportsProfile (G := G) 2).card := by
  have h01 : Disjoint (exceptionalSupportsProfile (G := G) 0)
        (exceptionalSupportsProfile (G := G) 1) :=
    exceptionalSupportsProfile_pair_disjoint 0 1 (by decide)
  have h02 : Disjoint (exceptionalSupportsProfile (G := G) 0)
        (exceptionalSupportsProfile (G := G) 2) :=
    exceptionalSupportsProfile_pair_disjoint 0 2 (by decide)
  have h12 : Disjoint (exceptionalSupportsProfile (G := G) 1)
        (exceptionalSupportsProfile (G := G) 2) :=
    exceptionalSupportsProfile_pair_disjoint 1 2 (by decide)
  have h0 : Disjoint (exceptionalSupportsProfile (G := G) 0)
      (exceptionalSupportsProfile (G := G) 1 ∪
        exceptionalSupportsProfile (G := G) 2) := by
    apply Finset.disjoint_left.mpr
    intro S hs ht
    rcases Finset.mem_union.mp ht with h1 | h2
    · exact (Finset.disjoint_left.mp h01) hs h1
    · exact (Finset.disjoint_left.mp h02) hs h2
  rw [exceptionalSupports_eq_three_profile_union,
    Finset.card_union_of_disjoint h0, Finset.card_union_of_disjoint h12]
  omega







end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
      (@Couret.STROBO2TORS.exceptionalSupports.{p2m_u_0} G inst inst_1 inst_2))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
          (@Couret.STROBO2TORS.exceptionalSupportsProfile.{p2m_u_0} G inst inst_1 inst_2
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
          (@Couret.STROBO2TORS.exceptionalSupportsProfile.{p2m_u_0} G inst inst_1 inst_2
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@Couret.STROBO2TORS.exceptionalSupportsProfile.{p2m_u_0} G inst inst_1 inst_2
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) := @_root_.Couret.STROBO2TORS.p2m_local_exceptionalSupports_card_profile_partition

