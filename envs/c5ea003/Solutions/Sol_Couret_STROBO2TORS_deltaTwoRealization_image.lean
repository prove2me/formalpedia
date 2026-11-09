-- Prove2me | solution 1 for Couret.STROBO2TORS.deltaTwoRealization_image
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:53:25.156008+00:00
-- url     : https://prove2.me/submissions/d6e154df-72be-45c7-b9f7-9118aeacc51f

import Aesop
import Definitions.Def_Couret_Strobo2TorsDeltaTwoCount_96c8f007ba6a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Theorems.Thm_Couret_STROBO2TORS_ordinaryPartner_inter_two_param
import Definitions.Def_Couret_Strobo2TorsDeltaOrdinaryCount_91279c99d3e0

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
Exact count of the ordinary delta-two edges, with zero allowed.

Parameters (a,u,b) have u a nonzero element of G[2] and b outside
{a,a+u}. They represent the ordered pair
({a,a+u,b}, {a,a+u,b+u}). Each ordered pair has precisely two
parameters, according to the choice a or a+u in its common pair.
The graph handshake supplies the second factor of two.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

private theorem deltaTwo_ne_add_self (a u : G) (hu0 : u ≠ 0) :
    a ≠ a + u := by
  intro h
  apply hu0
  exact (add_left_cancel (show a + 0 = a + u by simpa using h)).symm

private theorem deltaTwo_source_card (a u b : G)
    (hu0 : u ≠ 0) (hba : b ≠ a) (hbau : b ≠ a + u) :
    ({a, a + u, b} : Finset G).card = 3 := by
  simp [deltaTwo_ne_add_self a u hu0, hba.symm, hbau.symm]

private theorem deltaTwo_target_translate (a u b : G) (hu : u + u = 0) :
    ({a, a + u, b + u} : Finset G) =
      translateSupport ({a, a + u, b} : Finset G) u := by
  rw [translateSupport_three]
  have hshift : (a + u) + u = a := by simp [add_assoc, hu]
  rw [hshift]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem deltaTwo_inter (a u b : G)
    (hu0 : u ≠ 0) (hba : b ≠ a) (hbau : b ≠ a + u) :
    ({a, a + u, b} : Finset G) ∩ {a, a + u, b + u} = {a, a + u} := by
  have hbbu := deltaTwo_ne_add_self b u hu0
  ext x
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hy⟩
    rcases hx with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rcases hy with h | h | h
      · exact (hba h).elim
      · exact (hbau h).elim
      · exact (hbbu h).elim
  · rintro (rfl | rfl) <;> simp





variable [Fintype G]







theorem mem_deltaTwoParameters (a u b : G) :
    (⟨(a,u),b⟩ : DeltaTwoParameter G) ∈ deltaTwoParameters ↔
      u + u = 0 ∧ u ≠ 0 ∧ b ≠ a ∧ b ≠ a + u := by
  simp only [deltaTwoParameters, Finset.mem_sigma, Finset.mem_product,
    Finset.mem_univ, true_and, Finset.mem_erase, mem_twoTorsion,
    Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  tauto



attribute [local instance] Classical.propDecidable



theorem mem_deltaTwoOrderedPairs (S T : Finset G) :
    (S,T) ∈ deltaTwoOrderedPairs ↔
      S.card = 3 ∧ T.card = 3 ∧ OrdinaryPartner S T ∧ (S ∩ T).card = 2 := by
  simp only [deltaTwoOrderedPairs, Finset.mem_filter, Finset.mem_product,
    mem_tripleSupports]
  tauto

private theorem deltaTwoRealization_mem (a u b : G)
    (hu : u + u = 0) (hu0 : u ≠ 0) (hba : b ≠ a) (hbau : b ≠ a + u) :
    deltaTwoRealization (⟨(a,u),b⟩ : DeltaTwoParameter G) ∈ deltaTwoOrderedPairs := by
  apply (mem_deltaTwoOrderedPairs _ _).mpr
  have hS := deltaTwo_source_card a u b hu0 hba hbau
  have hT : ({a, a + u, b + u} : Finset G).card = 3 := by
    rw [deltaTwo_target_translate a u b hu, translateSupport_card]
    exact hS
  refine ⟨hS, hT, ⟨u, hu, deltaTwo_target_translate a u b hu⟩, ?_⟩
  rw [deltaTwo_inter a u b hu0 hba hbau]
  simp [deltaTwo_ne_add_self a u hu0]

theorem p2m_local_deltaTwoRealization_image :
    (deltaTwoParameters : Finset (DeltaTwoParameter G)).image deltaTwoRealization =
      deltaTwoOrderedPairs := by
  ext p
  rcases p with ⟨S,T⟩
  constructor
  · intro h
    obtain ⟨⟨⟨a,u⟩,b⟩, hp, heq⟩ := Finset.mem_image.mp h
    obtain ⟨hu, hu0, hba, hbau⟩ := (mem_deltaTwoParameters a u b).mp hp
    rw [← heq]
    exact deltaTwoRealization_mem a u b hu hu0 hba hbau
  · intro hp
    obtain ⟨hS, _, hOrd, hI⟩ := (mem_deltaTwoOrderedPairs S T).mp hp
    obtain ⟨a,u,b,hu,hu0,hba,hbau,hs,ht⟩ := ordinaryPartner_inter_two_param S T hS hOrd hI
    refine Finset.mem_image.mpr ⟨⟨(a,u),b⟩,
      (mem_deltaTwoParameters a u b).mpr ⟨hu,hu0,hba,hbau⟩, ?_⟩
    change ({a,a+u,b}, {a,a+u,b+u}) = (S,T)
    rw [hs,ht]














end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G)))
    (@Finset.image.{p2m_u_0, p2m_u_0} (Couret.STROBO2TORS.DeltaTwoParameter.{p2m_u_0} G)
      (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
      (fun a b =>
        @instDecidableEqProd.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G)
          (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b)
          (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b) a b)
      (@Couret.STROBO2TORS.deltaTwoRealization.{p2m_u_0} G inst inst_1)
      (@Couret.STROBO2TORS.deltaTwoParameters.{p2m_u_0} G inst inst_1 inst_2))
    (@Couret.STROBO2TORS.deltaTwoOrderedPairs.{p2m_u_0} G inst inst_1 inst_2) := @_root_.Couret.STROBO2TORS.p2m_local_deltaTwoRealization_image

