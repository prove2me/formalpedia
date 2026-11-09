-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinaryFibres_eq_profile_union_alternative
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:26:06.672734+00:00
-- url     : https://prove2.me/submissions/0c5d793d-9d4d-4077-ab3e-234adb8f9a3c

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

/-- Every ordinary complete fibre has a well-defined 2-torsion profile j
between zero and three. -/
private theorem ordinaryFibres_profile_exists (F : Finset (Finset G))
    (hF : F ∈ (ordinaryFibres : Finset (Finset (Finset G)))) :
    ∃ j : ℕ, j ≤ 3 ∧
      F ∈ (ordinaryFibresProfile (G := G) j) := by
  have hAll : F ∈ (allSquareFibres : Finset (Finset (Finset G))) :=
    (Finset.mem_filter.mp hF).1
  obtain ⟨S, hS, hSF⟩ := Finset.mem_image.mp hAll
  have hS3 : S.card = 3 := (mem_tripleSupports S).mp hS
  have hSmem : S ∈ F := by
    rw [← hSF]
    exact (mem_squareFibre S S).mpr ⟨hS3, fun _ => rfl⟩
  let j : ℕ := (S ∩ (twoTorsion : Finset G)).card
  have hj : j ≤ 3 := by
    dsimp [j]
    calc
      (S ∩ (twoTorsion : Finset G)).card ≤ S.card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = 3 := hS3
  refine ⟨j, hj, Finset.mem_filter.mpr ⟨hF, ?_⟩⟩
  exact ⟨S, hSmem, rfl⟩

/-- The four profile strata exhaust ordinary complete square fibres.
A profile is intrinsic to a complete ordinary fibre. -/
theorem p2m_local_ordinaryFibres_eq_profile_union_alternative :
    (ordinaryFibres : Finset (Finset (Finset G))) =
      ordinaryFibresProfile 0 ∪
        (ordinaryFibresProfile 1 ∪
          (ordinaryFibresProfile 2 ∪ ordinaryFibresProfile 3)) := by
  ext F
  constructor
  · intro hF
    obtain ⟨j, hj, hProfile⟩ := ordinaryFibres_profile_exists F hF
    have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · rw [h0] at hProfile
      exact Finset.mem_union.mpr (Or.inl hProfile)
    · rw [h1] at hProfile
      exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_union.mpr (Or.inl hProfile)))
    · rw [h2] at hProfile
      exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_union.mpr
          (Or.inr (Finset.mem_union.mpr (Or.inl hProfile)))))
    · rw [h3] at hProfile
      exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_union.mpr
          (Or.inr (Finset.mem_union.mpr (Or.inr hProfile)))))
  · intro hF
    rcases Finset.mem_union.mp hF with h0 | hRest
    · exact (Finset.mem_filter.mp h0).1
    · rcases Finset.mem_union.mp hRest with h1 | hRest
      · exact (Finset.mem_filter.mp h1).1
      · rcases Finset.mem_union.mp hRest with h2 | h3
        · exact (Finset.mem_filter.mp h2).1
        · exact (Finset.mem_filter.mp h3).1









end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
    (@Couret.STROBO2TORS.ordinaryFibres.{p2m_u_0} G inst inst_1 inst_2)
    (@Union.union.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@Finset.instUnion.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) fun a b =>
        @Finset.decidableEq.{p2m_u_0} (Finset.{p2m_u_0} G) (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b) a b)
      (@Couret.STROBO2TORS.ordinaryFibresProfile.{p2m_u_0} G inst inst_1 inst_2
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Union.union.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
        (@Finset.instUnion.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) fun a b =>
          @Finset.decidableEq.{p2m_u_0} (Finset.{p2m_u_0} G) (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b) a
            b)
        (@Couret.STROBO2TORS.ordinaryFibresProfile.{p2m_u_0} G inst inst_1 inst_2
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Union.union.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
          (@Finset.instUnion.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) fun a b =>
            @Finset.decidableEq.{p2m_u_0} (Finset.{p2m_u_0} G) (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b) a
              b)
          (@Couret.STROBO2TORS.ordinaryFibresProfile.{p2m_u_0} G inst inst_1 inst_2
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@Couret.STROBO2TORS.ordinaryFibresProfile.{p2m_u_0} G inst inst_1 inst_2
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))) := @_root_.Couret.STROBO2TORS.p2m_local_ordinaryFibres_eq_profile_union_alternative

