-- Prove2me | solution 1 for AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS.expected_components_eq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:43:55.618884+00:00
-- url     : https://prove2.me/submissions/dd9cdaeb-ebfa-4bac-8511-670429251b22

import Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_MappingComponents
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Completing the rooted forest count

This file adds a carrier-polymorphic version of the rooted-forest definitions
from `ForestCount.lean`.  The immediate target is the depth-one decomposition:
for a forest whose root set is not all vertices, at least one non-root has a
root as parent.
-/

open scoped BigOperators

namespace AnalyticCombinatorics.Ch2.Mappings.ForestCountNS.Complete

noncomputable section

lemma sum_nonempty_finsets_by_card {β : Type*} [DecidableEq β] [Fintype β]
    (f : ℕ → ℕ) :
    (∑ S : {S : Finset β // S.Nonempty}, f S.1.card) =
      ∑ i ∈ Finset.range (Fintype.card β),
        Nat.choose (Fintype.card β) (i + 1) * f (i + 1) := by
  classical
  let U : Finset β := Finset.univ
  have hsub :
      (∑ S : {S : Finset β // S.Nonempty}, f S.1.card) =
        ∑ S ∈ (Finset.univ : Finset (Finset β)) with S.Nonempty, f S.card := by
    simpa using
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset (Finset β)))
        (f := fun S : Finset β => f S.card)
        (p := fun S : Finset β => S.Nonempty))
  have huniv : (Finset.univ : Finset (Finset β)) = U.powerset := by
    ext S
    simp [U]
  have hinner (j : ℕ) :
      (∑ S ∈ U.powersetCard j, if S.Nonempty then f S.card else 0) =
        Nat.choose U.card j * (if j = 0 then 0 else f j) := by
    by_cases hj : j = 0
    · subst j
      simp
    · calc
        (∑ S ∈ U.powersetCard j, if S.Nonempty then f S.card else 0) =
            ∑ S ∈ U.powersetCard j, f S.card := by
            refine Finset.sum_congr rfl ?_
            intro S hS
            have hScard : S.card = j := (Finset.mem_powersetCard.mp hS).2
            have hnon : S.Nonempty := by
              rw [← Finset.card_pos, hScard]
              omega
            simp [hnon]
        _ = Nat.choose U.card j • f j := by
            simpa using
              (Finset.sum_powersetCard (n := j) (s := U) (f := f))
        _ = Nat.choose U.card j * f j := by
            simp
        _ = Nat.choose U.card j * (if j = 0 then 0 else f j) := by
            simp [hj]
  calc
    (∑ S : {S : Finset β // S.Nonempty}, f S.1.card)
        = ∑ S ∈ U.powerset with S.Nonempty, f S.card := by
          rw [hsub, huniv]
    _ = ∑ S ∈ U.powerset, if S.Nonempty then f S.card else 0 := by
          rw [Finset.sum_filter]
    _ = ∑ j ∈ Finset.range (U.card + 1),
          ∑ S ∈ U.powersetCard j, if S.Nonempty then f S.card else 0 := by
          rw [Finset.sum_powerset]
    _ = ∑ j ∈ Finset.range (U.card + 1),
          Nat.choose U.card j * (if j = 0 then 0 else f j) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          exact hinner j
    _ = ∑ i ∈ Finset.range U.card, Nat.choose U.card (i + 1) * f (i + 1) := by
          rw [Finset.sum_range_succ']
          simp
    _ = ∑ i ∈ Finset.range (Fintype.card β),
          Nat.choose (Fintype.card β) (i + 1) * f (i + 1) := by
          simp [U]

end
end AnalyticCombinatorics.Ch2.Mappings.ForestCountNS.Complete

/-!
# Connected random mappings

This file banks the iteration-level periodic-core facts used in the standard
cyclic-core decomposition of connected mappings.  The exact enumeration is not
completed here.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS

noncomputable section

open AnalyticCombinatorics.Ch2.Mappings.ForestCountNS
open AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

lemma permSingleCycle_iff_isCycle_support_full_of_two_le {α : Type*}
    [DecidableEq α] [Fintype α] {σ : Equiv.Perm α}
    (hα : 2 ≤ Fintype.card α) :
    PermSingleCycle σ ↔ σ.IsCycle ∧ σ.support.card = Fintype.card α := by
  constructor
  · intro hσ
    have hmove : ∀ x : α, σ x ≠ x := by
      intro x hxfix
      rcases Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card α) x with ⟨y, hy⟩
      rcases hσ x y with ⟨m, hm⟩
      have hfixed : σ^[m] x = x := Function.iterate_fixed hxfix m
      exact hy (hm.symm.trans hfixed)
    have hsupp : σ.support = Finset.univ := by
      ext x
      simp [Equiv.Perm.mem_support, hmove x]
    refine ⟨?_, by rw [hsupp, Finset.card_univ]⟩
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card α)
    refine ⟨x, hmove x, ?_⟩
    intro y _hy
    rcases hσ x y with ⟨m, hm⟩
    refine ⟨(m : ℤ), ?_⟩
    have hpow : (σ ^ m) x = y := by
      change (⇑(σ ^ m)) x = y
      rw [Equiv.Perm.coe_pow]
      exact hm
    simpa [zpow_natCast] using hpow
  · rintro ⟨hcycle, hsupp_card⟩ x y
    have hsupp : σ.support = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa using hsupp_card
    have hx : σ x ≠ x := by
      exact Equiv.Perm.mem_support.mp (by simp [hsupp])
    have hy : σ y ≠ y := by
      exact Equiv.Perm.mem_support.mp (by simp [hsupp])
    rcases (hcycle.sameCycle hx hy).exists_nat_pow_eq with ⟨m, hm⟩
    have hiter : σ^[m] x = y := by
      change (⇑σ)^[m] x = y
      rw [← Equiv.Perm.coe_pow]
      exact hm
    exact ⟨m, hiter⟩

lemma cycleType_singleton_full_iff_permSingleCycle {α : Type*}
    [DecidableEq α] [Fintype α] {σ : Equiv.Perm α}
    (hα : 2 ≤ Fintype.card α) :
    σ.cycleType = ({Fintype.card α} : Multiset ℕ) ↔ PermSingleCycle σ := by
  constructor
  · intro htype
    have hcycle : σ.IsCycle := by
      rw [← Equiv.Perm.card_cycleType_eq_one]
      rw [htype]
      simp
    have hsupp : σ.support.card = Fintype.card α := by
      have hsum := Equiv.Perm.sum_cycleType σ
      rw [htype] at hsum
      simpa using hsum.symm
    exact (permSingleCycle_iff_isCycle_support_full_of_two_le (σ := σ) hα).mpr
      ⟨hcycle, hsupp⟩
  · intro hsingle
    rcases (permSingleCycle_iff_isCycle_support_full_of_two_le (σ := σ) hα).mp hsingle with
      ⟨hcycle, hsupp⟩
    rw [hcycle.cycleType, hsupp]

theorem card_permSingleCycle_of_two_le {α : Type*} [DecidableEq α] [Fintype α]
    (hα : 2 ≤ Fintype.card α) :
    Fintype.card {σ : Equiv.Perm α // PermSingleCycle σ} =
      (Fintype.card α - 1).factorial := by
  classical
  have hsub :
      Fintype.card {σ : Equiv.Perm α // PermSingleCycle σ} =
        ({g | g.cycleType = ({Fintype.card α} : Multiset ℕ)} :
          Finset (Equiv.Perm α)).card := by
    rw [Fintype.card_subtype]
    apply congrArg Finset.card
    ext g
    simp [cycleType_singleton_full_iff_permSingleCycle (σ := g) hα]
  rw [hsub]
  rw [Equiv.Perm.card_of_cycleType_singleton hα (le_rfl : Fintype.card α ≤ Fintype.card α)]
  simp

theorem card_permSingleCycle_of_card_le_one {α : Type*} [DecidableEq α] [Fintype α]
    (hα : Fintype.card α ≤ 1) :
    Fintype.card {σ : Equiv.Perm α // PermSingleCycle σ} = 1 := by
  classical
  have hsub : ∀ x y : α, x = y := Fintype.card_le_one_iff.mp hα
  refine Fintype.card_eq_one_iff.mpr ⟨⟨1, ?_⟩, ?_⟩
  · intro x y
    exact ⟨0, hsub x y⟩
  · intro σ
    apply Subtype.ext
    apply Equiv.Perm.ext
    intro x
    exact hsub _ _

theorem card_permSingleCycle {α : Type*} [DecidableEq α] [Fintype α] :
    Fintype.card {σ : Equiv.Perm α // PermSingleCycle σ} =
      (Fintype.card α - 1).factorial := by
  classical
  by_cases hα : 2 ≤ Fintype.card α
  · exact card_permSingleCycle_of_two_le hα
  · have hle : Fintype.card α ≤ 1 := by omega
    have hsmall : Fintype.card α = 0 ∨ Fintype.card α = 1 := by omega
    rw [card_permSingleCycle_of_card_le_one hle]
    rcases hsmall with h0 | h1
    · simp [h0]
    · simp [h1]

end
end AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS

/-!
# Components of random mappings

The component count is defined as the number of nonempty single-cycle
restrictions of the permutation induced by a mapping on its periodic core.  A
candidate cycle `C` of a map is counted exactly when the ambient map restricts
to a cyclic permutation on `C`; this is equivalent to being one cycle of the
periodic-core permutation.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS

noncomputable section

open AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS
open AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

lemma componentCount_eq_mapCycle_card {n : ℕ} (f : Fin n → Fin n) :
    componentCount f = Fintype.card (MapCycleOfMap f) := by
  exact @Fintype.card_congr (CoreCycleOfMap f) (MapCycleOfMap f)
    (coreCycleOfMapFintype f) inferInstance (coreCycleMapCycleEquiv f)

lemma card_mapsRespectingCandidate {n : ℕ} (A : CandidateCycle n) :
    Fintype.card (MapsRespectingCandidate A) =
      n ^ (n - candidateCard A) := by
  classical
  calc
    Fintype.card (MapsRespectingCandidate A) =
        Fintype.card ({x : Fin n // x ∉ candidateSupport A} → Fin n) := by
          exact Fintype.card_congr (mapsRespectingCandidateEquiv A)
    _ = n ^ Fintype.card {x : Fin n // x ∉ candidateSupport A} := by
          rw [Fintype.card_fun, Fintype.card_fin]
    _ = n ^ (n - candidateCard A) := by
          congr 1
          change Fintype.card {x : Fin n // x ∉ candidateSupport A} =
            n - (candidateSupport A).card
          rw [Fintype.card_subtype_compl (fun x : Fin n => x ∈ candidateSupport A)]
          simp [Fintype.card_fin]

lemma sum_componentCount_eq_candidate_maps (n : ℕ) :
    (∑ f : Fin n → Fin n, componentCount f) =
      ∑ A : CandidateCycle n, Fintype.card (MapsRespectingCandidate A) := by
  classical
  calc
    (∑ f : Fin n → Fin n, componentCount f) =
        ∑ f : Fin n → Fin n, Fintype.card (MapCycleOfMap f) := by
          refine Finset.sum_congr rfl ?_
          intro f _
          exact componentCount_eq_mapCycle_card f
    _ = Fintype.card (Sigma fun f : Fin n → Fin n => MapCycleOfMap f) := by
          exact Fintype.card_sigma.symm
    _ = Fintype.card (Sigma fun A : CandidateCycle n => MapsRespectingCandidate A) := by
          exact Fintype.card_congr (mapCycleSwapEquiv n)
    _ = ∑ A : CandidateCycle n, Fintype.card (MapsRespectingCandidate A) := by
          exact Fintype.card_sigma

lemma candidate_maps_sum_by_card (n : ℕ) :
    (∑ A : CandidateCycle n, Fintype.card (MapsRespectingCandidate A)) =
      ∑ k ∈ Finset.Icc 1 n,
        Nat.choose n k * (k - 1).factorial * n ^ (n - k) := by
  classical
  calc
    (∑ A : CandidateCycle n, Fintype.card (MapsRespectingCandidate A)) =
        ∑ A : CandidateCycle n, n ^ (n - candidateCard A) := by
          refine Finset.sum_congr rfl ?_
          intro A _
          exact card_mapsRespectingCandidate A
    _ =
        ∑ C : {C : Finset (Fin n) // C.Nonempty},
          ∑ σ : {σ : Equiv.Perm C.1 // PermSingleCycle σ},
            n ^ (n - C.1.card) := by
          rw [Fintype.sum_sigma]
          rfl
    _ =
        ∑ C : {C : Finset (Fin n) // C.Nonempty},
          (C.1.card - 1).factorial * n ^ (n - C.1.card) := by
          refine Finset.sum_congr rfl ?_
          intro C _
          simp [card_permSingleCycle, Fintype.card_coe, mul_comm]
    _ =
        ∑ i ∈ Finset.range n,
          Nat.choose n (i + 1) *
            ((i + 1 - 1).factorial * n ^ (n - (i + 1))) := by
          simpa [Fintype.card_fin] using
            (AnalyticCombinatorics.Ch2.Mappings.ForestCountNS.Complete.sum_nonempty_finsets_by_card
              (β := Fin n)
              (f := fun k : ℕ => (k - 1).factorial * n ^ (n - k)))
    _ =
        ∑ k ∈ Finset.Icc 1 n,
          Nat.choose n k * (k - 1).factorial * n ^ (n - k) := by
          simpa [Finset.Ico_add_one_right_eq_Icc, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc, mul_assoc] using
            (Finset.sum_Ico_eq_sum_range
              (f := fun k : ℕ =>
                Nat.choose n k * (k - 1).factorial * n ^ (n - k))
              1 (n + 1)).symm

theorem sum_componentCount_eq (n : ℕ) :
    (∑ f : Fin n → Fin n, componentCount f) =
      ∑ k ∈ Finset.Icc 1 n,
        Nat.choose n k * (k - 1).factorial * n ^ (n - k) := by
  rw [sum_componentCount_eq_candidate_maps n, candidate_maps_sum_by_card n]

lemma descFactorial_eq_k_mul_choose_mul_pred_factorial {n k : ℕ} (hk : 0 < k) :
    n.descFactorial k = k * (Nat.choose n k * (k - 1).factorial) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  simp [Nat.factorial_succ]
  ring

lemma expectation_term_eq_desc {n k : ℕ} (hn : 0 < n)
    (hk : k ∈ Finset.Icc 1 n) :
    (((Nat.choose n k * (k - 1).factorial * n ^ (n - k) : ℕ) : ℝ) /
        (n : ℝ) ^ n) =
      (n.descFactorial k : ℝ) / ((k : ℝ) * (n : ℝ) ^ k) := by
  have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
  have hkle : k ≤ n := (Finset.mem_Icc.mp hk).2
  have hnne : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  have hkne : (k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hkpos
  have htail_ne : (n : ℝ) ^ (n - k) ≠ 0 := pow_ne_zero _ hnne
  have hpowk_ne : (n : ℝ) ^ k ≠ 0 := pow_ne_zero _ hnne
  have hsplit : n = (n - k) + k := by omega
  have hpow_split : (n : ℝ) ^ n = (n : ℝ) ^ (n - k) * (n : ℝ) ^ k := by
    calc
      (n : ℝ) ^ n = (n : ℝ) ^ ((n - k) + k) := by
        exact congrArg (fun e : ℕ => (n : ℝ) ^ e) hsplit
      _ = (n : ℝ) ^ (n - k) * (n : ℝ) ^ k := by
        rw [pow_add]
  have hdesc :
      (n.descFactorial k : ℝ) =
        (k : ℝ) * ((Nat.choose n k * (k - 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast descFactorial_eq_k_mul_choose_mul_pred_factorial (n := n) (k := k) hkpos
  rw [hpow_split, hdesc]
  push_cast
  field_simp [hkne, htail_ne, hpowk_ne]

end
end AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS

open AnalyticCombinatorics AnalyticCombinatorics.Ch2 AnalyticCombinatorics.Ch2.Mappings AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS
open Filter Asymptotics
open scoped BigOperators Topology
open AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS
open AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS
theorem solution {n : ℕ} (hn : 0 < n) :
    (∑ f : Fin n → Fin n, (componentCount f : ℝ)) / (n : ℝ)^n
      = ∑ k ∈ Finset.Icc 1 n,
          (n.descFactorial k : ℝ) / ((k : ℝ) * (n : ℝ)^k) := by
  classical
  have hsum_nat := sum_componentCount_eq n
  have hsum_real :
      (∑ f : Fin n → Fin n, (componentCount f : ℝ)) =
        ∑ k ∈ Finset.Icc 1 n,
          ((Nat.choose n k * (k - 1).factorial * n ^ (n - k) : ℕ) : ℝ) := by
    exact_mod_cast hsum_nat
  calc
    (∑ f : Fin n → Fin n, (componentCount f : ℝ)) / (n : ℝ)^n =
        (∑ k ∈ Finset.Icc 1 n,
          ((Nat.choose n k * (k - 1).factorial * n ^ (n - k) : ℕ) : ℝ)) /
            (n : ℝ)^n := by
          rw [hsum_real]
    _ =
        ∑ k ∈ Finset.Icc 1 n,
          (((Nat.choose n k * (k - 1).factorial * n ^ (n - k) : ℕ) : ℝ) /
            (n : ℝ)^n) := by
          rw [Finset.sum_div]
    _ =
        ∑ k ∈ Finset.Icc 1 n,
          (n.descFactorial k : ℝ) / ((k : ℝ) * (n : ℝ)^k) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          exact expectation_term_eq_desc hn hk
