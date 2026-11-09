-- Prove2me | solution 1 for Couret.STROBO2TORS.deltaTwoRealization_preimage
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:01:17.74751+00:00
-- url     : https://prove2.me/submissions/23b44276-0075-4727-80aa-b0351d3103d6

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
import Theorems.Thm_Couret_STROBO2TORS_deltaTwoRealization_image
import Theorems.Thm_Couret_STROBO2TORS_translateSupport_injective_on_two_torsion
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

private theorem deltaTwo_sdiff (a u b : G)
    (hu0 : u ≠ 0) (hba : b ≠ a) (hbau : b ≠ a + u) :
    ({a, a + u, b} : Finset G) \ {a, a + u, b + u} = {b} := by
  have hbbu := deltaTwo_ne_add_self b u hu0
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hy⟩
    rcases hx with rfl | rfl | rfl
    · exact (hy (Or.inl rfl)).elim
    · exact (hy (Or.inr (Or.inl rfl))).elim
    · rfl
  · rintro rfl
    exact ⟨Or.inr (Or.inr rfl), fun h => h.elim hba (fun h => h.elim hbau hbbu)⟩



variable [Fintype G]







theorem mem_deltaTwoParameters (a u b : G) :
    (⟨(a,u),b⟩ : DeltaTwoParameter G) ∈ deltaTwoParameters ↔
      u + u = 0 ∧ u ≠ 0 ∧ b ≠ a ∧ b ≠ a + u := by
  simp only [deltaTwoParameters, Finset.mem_sigma, Finset.mem_product,
    Finset.mem_univ, true_and, Finset.mem_erase, mem_twoTorsion,
    Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  tauto



attribute [local instance] Classical.propDecidable









private theorem deltaTwoRealization_swap_a (a u b : G) (hu : u + u = 0) :
    deltaTwoRealization (⟨(a+u,u),b⟩ : DeltaTwoParameter G) =
      deltaTwoRealization (⟨(a,u),b⟩ : DeltaTwoParameter G) := by
  have hshift : (a + u) + u = a := by simp [add_assoc, hu]
  apply Prod.ext
  · change ({a+u,(a+u)+u,b} : Finset G) = {a,a+u,b}
    rw [hshift]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · change ({a+u,(a+u)+u,b+u} : Finset G) = {a,a+u,b+u}
    rw [hshift]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

/-- The two choices of a in the common pair are the entire multiplicity
of the ordered realization map. -/
theorem p2m_local_deltaTwoRealization_preimage (P : Finset G × Finset G)
    (hP : P ∈ deltaTwoOrderedPairs) :
    ((deltaTwoParameters : Finset (DeltaTwoParameter G)).filter
      (fun p => deltaTwoRealization p = P)).card = 2 := by
  rw [← deltaTwoRealization_image] at hP
  obtain ⟨⟨⟨a,u⟩,b⟩, hp, rfl⟩ := Finset.mem_image.mp hP
  obtain ⟨hu, hu0, hba, hbau⟩ := (mem_deltaTwoParameters a u b).mp hp
  have hfilter :
      ((deltaTwoParameters : Finset (DeltaTwoParameter G)).filter
        (fun p => deltaTwoRealization p = deltaTwoRealization ⟨(a,u),b⟩)) =
      {⟨(a,u),b⟩, ⟨(a+u,u),b⟩} := by
    ext p
    rcases p with ⟨⟨c,v⟩,e⟩
    rw [Finset.mem_filter]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hq, heq⟩
      obtain ⟨hv, hv0, hec, hecv⟩ := (mem_deltaTwoParameters c v e).mp hq
      have hS := congrArg Prod.fst heq
      have hT := congrArg Prod.snd heq
      change ({c,c+v,e} : Finset G) = {a,a+u,b} at hS
      change ({c,c+v,e+v} : Finset G) = {a,a+u,b+u} at hT
      have hvu : v = u := by
        apply translateSupport_injective_on_two_torsion ({a,a+u,b} : Finset G)
          (deltaTwo_source_card a u b hu0 hba hbau) v u hv hu
        calc
          translateSupport ({a,a+u,b} : Finset G) v =
              translateSupport ({c,c+v,e} : Finset G) v := congrArg (fun X => translateSupport X v) hS.symm
          _ = {c,c+v,e+v} := (deltaTwo_target_translate c v e hv).symm
          _ = {a,a+u,b+u} := hT
          _ = translateSupport ({a,a+u,b} : Finset G) u := deltaTwo_target_translate a u b hu
      have heb : e = b := by
        have hd := congrArg (fun q : Finset G × Finset G => q.1 \ q.2) heq
        change ({c,c+v,e} : Finset G) \ {c,c+v,e+v} =
          ({a,a+u,b} : Finset G) \ {a,a+u,b+u} at hd
        rw [deltaTwo_sdiff c v e hv0 hec hecv,
          deltaTwo_sdiff a u b hu0 hba hbau] at hd
        exact Finset.singleton_inj.mp hd
      subst v
      subst e
      have hc : c = a ∨ c = a + u := by
        have hi := congrArg (fun q : Finset G × Finset G => q.1 ∩ q.2) heq
        change ({c,c+u,b} : Finset G) ∩ {c,c+u,b+u} =
          ({a,a+u,b} : Finset G) ∩ {a,a+u,b+u} at hi
        rw [deltaTwo_inter c u b hv0 hec hecv,
          deltaTwo_inter a u b hu0 hba hbau] at hi
        have hcMem : c ∈ ({a,a+u} : Finset G) := by
          rw [← hi]
          simp
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hcMem
      rcases hc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (heq | heq)
      · rw [heq]
        exact ⟨hp,rfl⟩
      · rw [heq]
        have hshift : (a+u)+u = a := by simp [add_assoc,hu]
        exact ⟨(mem_deltaTwoParameters (a+u) u b).mpr
          ⟨hu,hu0,hbau,by simpa only [hshift] using hba⟩,
          deltaTwoRealization_swap_a a u b hu⟩
  rw [hfilter]
  have hne : (⟨(a,u),b⟩ : DeltaTwoParameter G) ≠ ⟨(a+u,u),b⟩ := by
    intro h
    exact deltaTwo_ne_add_self a u hu0 (congrArg (fun p : DeltaTwoParameter G => p.1.1) h)
  simp [hne]










end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (P : Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G)),
  @Membership.mem.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
      (Finset.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G)))
      (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
        (Finset.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G)))
        (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
        (@Finset.instSetLike.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))))
      (@Couret.STROBO2TORS.deltaTwoOrderedPairs.{p2m_u_0} G inst inst_1 inst_2) P →
    @Eq.{1} Nat
      (@Finset.card.{p2m_u_0} (Couret.STROBO2TORS.DeltaTwoParameter.{p2m_u_0} G)
        (@Finset.filter.{p2m_u_0} (Couret.STROBO2TORS.DeltaTwoParameter.{p2m_u_0} G)
          (fun p =>
            @Eq.{p2m_u_0 + 1} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
              (@Couret.STROBO2TORS.deltaTwoRealization.{p2m_u_0} G inst inst_1 p) P)
          (fun a =>
            @instDecidableEqProd.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G)
              (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b)
              (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b)
              (@Couret.STROBO2TORS.deltaTwoRealization.{p2m_u_0} G inst inst_1 a) P)
          (@Couret.STROBO2TORS.deltaTwoParameters.{p2m_u_0} G inst inst_1 inst_2)))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) := @_root_.Couret.STROBO2TORS.p2m_local_deltaTwoRealization_preimage

