-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinaryFibres_eq_profile_union
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:26:11.005023+00:00
-- url     : https://prove2.me/submissions/9566e8fc-09f0-40d6-a8e6-277076a99d06

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibres_zeroFree_size
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]



/-- Partition into genuine full ordinary fibres of profiles 0,1,2,3.
This decomposition remains valid even when |G[2]| is 1 or 2. -/
theorem p2m_local_ordinaryFibres_eq_profile_union :
    (ordinaryFibres : Finset (Finset (Finset G))) =
      ordinaryFibresProfile 0 ∪
        (ordinaryFibresProfile 1 ∪
          (ordinaryFibresProfile 2 ∪ ordinaryFibresProfile 3)) := by
  ext F
  constructor
  · intro hOrd
    obtain ⟨S, hS3, hSF, _⟩ := ordinaryFibres_zeroFree_size F hOrd
    have hS : S ∈ F := by
      rw [← hSF]
      exact (mem_squareFibre S S).mpr ⟨hS3, fun _ => rfl⟩
    have hle : (S ∩ (twoTorsion : Finset G)).card ≤ 3 := by
      calc
        (S ∩ (twoTorsion : Finset G)).card ≤ S.card :=
          Finset.card_le_card Finset.inter_subset_left
        _ = 3 := hS3
    have hp : (S ∩ (twoTorsion : Finset G)).card = 0 ∨
        (S ∩ (twoTorsion : Finset G)).card = 1 ∨
        (S ∩ (twoTorsion : Finset G)).card = 2 ∨
        (S ∩ (twoTorsion : Finset G)).card = 3 := by omega
    rcases hp with h0 | h1 | h2 | h3
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨hOrd, S, hS, h0⟩))
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_union.mpr (Or.inl
          (Finset.mem_filter.mpr ⟨hOrd, S, hS, h1⟩))))
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_union.mpr (Or.inr
          (Finset.mem_union.mpr (Or.inl
            (Finset.mem_filter.mpr ⟨hOrd, S, hS, h2⟩))))))
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_union.mpr (Or.inr
          (Finset.mem_union.mpr (Or.inr
            (Finset.mem_filter.mpr ⟨hOrd, S, hS, h3⟩))))))
  · intro h
    rcases Finset.mem_union.mp h with h0 | h123
    · exact (Finset.mem_filter.mp h0).1
    · rcases Finset.mem_union.mp h123 with h1 | h23
      · exact (Finset.mem_filter.mp h1).1
      · rcases Finset.mem_union.mp h23 with h2 | h3
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
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))) := @_root_.Couret.STROBO2TORS.p2m_local_ordinaryFibres_eq_profile_union

