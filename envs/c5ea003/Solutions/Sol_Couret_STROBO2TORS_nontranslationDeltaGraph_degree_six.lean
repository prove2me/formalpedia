-- Prove2me | solution 1 for Couret.STROBO2TORS.nontranslationDeltaGraph_degree_six
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:56.473325+00:00
-- url     : https://prove2.me/submissions/8ebbed20-40a9-4a93-b85c-cbb54d082656

import Aesop
import Definitions.Def_Couret_Strobo2TorsDeltaExceptionalCount_9f9783d90924
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalPartner_normalized_inter
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports
import Theorems.Thm_Couret_STROBO2TORS_nontranslatedNeighbours_card_exceptional
import Theorems.Thm_Couret_STROBO2TORS_nontranslatedNeighbours_card_ordinary
import Theorems.Thm_Couret_STROBO2TORS_paired_orbits_disjoint
import Theorems.Thm_Couret_STROBO2TORS_paired_squareFibre_eq
import Theorems.Thm_Couret_STROBO2TORS_paired_support_card_three
import Theorems.Thm_Couret_STROBO2TORS_reflected_support_card_three
import Theorems.Thm_Couret_STROBO2TORS_triple_symmDiff_card_balance
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Definitions.Def_Couret_Strobo2TorsNontranslationUnordered_7692bff20374

set_option autoImplicit false

/-!
Unordered nontranslation collisions, split by symmetric-difference size.
The ambient group is finite abelian, supports have cardinality three, and
zero is permitted. An exceptional source has one delta-four neighbour and
`|G[2]| - 1` delta-six neighbours. Graph degree sums count unordered pairs
twice, so the final statements require no division in natural numbers.
-/

open scoped BigOperators symmDiff

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]











private theorem deltaCount_paired_nontranslatedNeighbours
    (a b d : G) (hd : d + d = 0) (hd0 : d ≠ 0)
    (hab : a + a ≠ b + b)
    (h3 : ((b - a) + (b - a)) + (b - a) = 0 ∨
      ((b - a) + (b - a)) + (b - a) = d) :
    nontranslatedNeighbours ({a, b, b + d} : Finset G) =
      torsionOrbit ({a, b + b - a, (b + b - a) + d} : Finset G) := by
  rw [nontranslatedNeighbours, paired_squareFibre_eq a b d hd hd0 hab,
    if_pos h3]
  have hdisj := paired_orbits_disjoint a b d hd hab
  ext T
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hOrd | hRef, hNotOrd⟩
    · exact (hNotOrd hOrd).elim
    · exact hRef
  · intro hRef
    exact ⟨Or.inr hRef, fun hOrd =>
      (Finset.disjoint_left.mp hdisj) hOrd hRef⟩

private theorem deltaCount_reflected_translate_delta
    (a b d u : G) (hd : d + d = 0) (hd0 : d ≠ 0)
    (hab : a + a ≠ b + b) (hu : u + u = 0)
    (h3 : ((b - a) + (b - a)) + (b - a) = 0 ∨
      ((b - a) + (b - a)) + (b - a) = d) :
    (({a, b, b + d} : Finset G) ∆
        translateSupport ({a, b + b - a, (b + b - a) + d} : Finset G) u).card =
      if u = 0 then 4 else 6 := by
  have hS := paired_support_card_three a b d hd hd0 hab
  have hR := reflected_support_card_three a b d hd hd0 hab h3
  have hT := (translateSupport_card
    ({a, b + b - a, (b + b - a) + d} : Finset G) u).trans hR
  have hbalance := triple_symmDiff_card_balance
    ({a, b, b + d} : Finset G)
    (translateSupport ({a, b + b - a, (b + b - a) + d} : Finset G) u) hS hT
  rw [exceptionalPartner_normalized_inter a b d u hd hab hu h3] at hbalance
  by_cases hu0 : u = 0
  · simp only [if_pos hu0, Finset.card_singleton] at hbalance ⊢
    omega
  · simp only [if_neg hu0, Finset.card_empty] at hbalance ⊢
    omega

private theorem deltaCount_paired_four_neighbours
    (a b d : G) (hd : d + d = 0) (hd0 : d ≠ 0)
    (hab : a + a ≠ b + b)
    (h3 : ((b - a) + (b - a)) + (b - a) = 0 ∨
      ((b - a) + (b - a)) + (b - a) = d) :
    nontranslationDeltaNeighbours ({a, b, b + d} : Finset G) 4 =
      {({a, b + b - a, (b + b - a) + d} : Finset G)} := by
  rw [nontranslationDeltaNeighbours,
    deltaCount_paired_nontranslatedNeighbours a b d hd hd0 hab h3]
  ext T
  constructor
  · intro hT
    obtain ⟨hOrbit, hFour⟩ := Finset.mem_filter.mp hT
    obtain ⟨u, hu, hTu⟩ := (mem_torsionOrbit _ T).mp hOrbit
    have hDelta := deltaCount_reflected_translate_delta a b d u hd hd0 hab hu h3
    have hu0 : u = 0 := by
      by_contra hne
      rw [if_neg hne] at hDelta
      rw [hTu] at hFour
      omega
    apply Finset.mem_singleton.mpr
    simpa [hu0, translateSupport] using hTu
  · intro hT
    have hTR := Finset.mem_singleton.mp hT
    subst T
    apply Finset.mem_filter.mpr
    constructor
    · exact (mem_torsionOrbit _ _).mpr ⟨0, by simp, by simp [translateSupport]⟩
    · have hDelta := deltaCount_reflected_translate_delta a b d 0 hd hd0 hab
        (by simp) h3
      simpa [translateSupport] using hDelta

private theorem deltaCount_paired_six_neighbours
    (a b d : G) (hd : d + d = 0) (hd0 : d ≠ 0)
    (hab : a + a ≠ b + b)
    (h3 : ((b - a) + (b - a)) + (b - a) = 0 ∨
      ((b - a) + (b - a)) + (b - a) = d) :
    nontranslationDeltaNeighbours ({a, b, b + d} : Finset G) 6 =
      (nontranslatedNeighbours ({a, b, b + d} : Finset G)).erase
        ({a, b + b - a, (b + b - a) + d} : Finset G) := by
  let R : Finset G := {a, b + b - a, (b + b - a) + d}
  have hRfourMem : R ∈ nontranslationDeltaNeighbours ({a, b, b + d} : Finset G) 4 := by
    rw [deltaCount_paired_four_neighbours a b d hd hd0 hab h3]
    simp [R]
  have hRfour : (({a, b, b + d} : Finset G) ∆ R).card = 4 :=
    (Finset.mem_filter.mp hRfourMem).2
  change nontranslationDeltaNeighbours ({a, b, b + d} : Finset G) 6 =
    (nontranslatedNeighbours ({a, b, b + d} : Finset G)).erase R
  ext T
  constructor
  · intro hT
    obtain ⟨hN, hSix⟩ := Finset.mem_filter.mp hT
    apply Finset.mem_erase.mpr
    refine ⟨?_, hN⟩
    intro hTR
    rw [hTR] at hSix
    omega
  · intro hT
    obtain ⟨hNotR, hN⟩ := Finset.mem_erase.mp hT
    have hOrbit := hN
    rw [deltaCount_paired_nontranslatedNeighbours a b d hd hd0 hab h3] at hOrbit
    obtain ⟨u, hu, hTu⟩ := (mem_torsionOrbit R T).mp hOrbit
    have hu0 : u ≠ 0 := by
      intro hzero
      apply hNotR
      simpa [hzero, translateSupport] using hTu
    apply Finset.mem_filter.mpr
    refine ⟨hN, ?_⟩
    rw [hTu]
    exact (deltaCount_reflected_translate_delta a b d u hd hd0 hab hu h3).trans
      (if_neg hu0)



/-- All other nontranslated partners of an exceptional source have delta six. -/
theorem nontranslationDeltaNeighbours_six_card_exceptional (S : Finset G)
    (hExc : S ∈ (exceptionalSupports : Finset (Finset G))) :
    (nontranslationDeltaNeighbours S 6).card =
      (twoTorsion : Finset G).card - 1 := by
  obtain ⟨_, T, he⟩ := (mem_exceptionalSupports S).mp hExc
  obtain ⟨a, b, d, u, hd, hd0, hab, hu, h3, hs, ht⟩ := he
  let R : Finset G := {a, b + b - a, (b + b - a) + d}
  have hSplit : nontranslationDeltaNeighbours S 6 = (nontranslatedNeighbours S).erase R := by
    simpa only [hs, R] using deltaCount_paired_six_neighbours a b d hd hd0 hab h3
  have hRmem : R ∈ nontranslatedNeighbours S := by
    rw [hs, deltaCount_paired_nontranslatedNeighbours a b d hd hd0 hab h3]
    exact (mem_torsionOrbit R R).mpr ⟨0, by simp, by simp [translateSupport]⟩
  rw [hSplit, Finset.card_erase_of_mem hRmem,
    nontranslatedNeighbours_card_exceptional S hExc]

private theorem deltaCount_neighbours_card_ordinary (S : Finset G) (k : ℕ)
    (hS : S.card = 3)
    (hNotExc : S ∉ (exceptionalSupports : Finset (Finset G))) :
    (nontranslationDeltaNeighbours S k).card = 0 := by
  have hEmpty : nontranslatedNeighbours S = ∅ := Finset.card_eq_zero.mp
    (nontranslatedNeighbours_card_ordinary S hS hNotExc)
  simp [nontranslationDeltaNeighbours, hEmpty]

theorem nontranslationDeltaGraph_degree (S : Finset G) (k : ℕ) :
    (nontranslationDeltaGraph (G := G) k).degree S =
      if S.card = 3 then (nontranslationDeltaNeighbours S k).card else 0 := by
  classical
  have hNeighbors : (nontranslationDeltaGraph (G := G) k).neighborFinset S =
      if S.card = 3 then nontranslationDeltaNeighbours S k else ∅ := by
    ext T
    by_cases hS : S.card = 3 <;> simp [nontranslationDeltaGraph, hS]
  change ((nontranslationDeltaGraph (G := G) k).neighborFinset S).card = _
  rw [hNeighbors]
  split_ifs <;> simp



/-- The delta-six nontranslation graph has degree h-1 at exceptional
supports and degree zero everywhere else. -/
theorem p2m_local_nontranslationDeltaGraph_degree_six (S : Finset G) :
    (nontranslationDeltaGraph (G := G) 6).degree S =
      if S ∈ (exceptionalSupports : Finset (Finset G))
      then (twoTorsion : Finset G).card - 1 else 0 := by
  rw [nontranslationDeltaGraph_degree]
  by_cases hS : S.card = 3
  · rw [if_pos hS]
    by_cases hExc : S ∈ (exceptionalSupports : Finset (Finset G))
    · rw [if_pos hExc]
      exact nontranslationDeltaNeighbours_six_card_exceptional S hExc
    · rw [if_neg hExc]
      exact deltaCount_neighbours_card_ordinary S 6 hS hExc
  · have hNotExc : S ∉ (exceptionalSupports : Finset (Finset G)) := by
      intro hExc
      exact hS ((mem_exceptionalSupports S).mp hExc).1
    rw [if_neg hS, if_neg hNotExc]












end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S : Finset.{p2m_u_0} G),
  @Eq.{1} Nat
    (@SimpleGraph.degree.{p2m_u_0} (Finset.{p2m_u_0} G)
      (@Couret.STROBO2TORS.nontranslationDeltaGraph.{p2m_u_0} G inst inst_1 inst_2
        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
      S
      (@Subtype.fintype.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Set.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@Set.instMembership.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@SimpleGraph.neighborSet.{p2m_u_0} (Finset.{p2m_u_0} G)
            (@Couret.STROBO2TORS.nontranslationDeltaGraph.{p2m_u_0} G inst inst_1 inst_2
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
            S))
        (fun a =>
          @SimpleGraph.neighborSet.memDecidable.{p2m_u_0} (Finset.{p2m_u_0} G)
            (@Couret.STROBO2TORS.nontranslationDeltaGraph.{p2m_u_0} G inst inst_1 inst_2
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
            S
            (@Couret.STROBO2TORS.nontranslationDeltaGraph_decidableRel.{p2m_u_0} G inst inst_1 inst_2
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
            a)
        (@Finset.fintype.{p2m_u_0} G inst_2)))
    (@ite.{1} Nat
      (@Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
          (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G)))
        (@Couret.STROBO2TORS.exceptionalSupports.{p2m_u_0} G inst inst_1 inst_2) S)
      (@Finset.decidableMem.{p2m_u_0} (Finset.{p2m_u_0} G) (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b) S
        (@Couret.STROBO2TORS.exceptionalSupports.{p2m_u_0} G inst inst_1 inst_2))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := @_root_.Couret.STROBO2TORS.p2m_local_nontranslationDeltaGraph_degree_six

