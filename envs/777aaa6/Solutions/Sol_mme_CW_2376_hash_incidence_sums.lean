-- Prove2me | solution 1 for mme_CW_2376_hash_incidence_sums
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:27:23.135639+00:00
-- url     : https://prove2.me/submissions/f6b10f31-fc85-424e-96d6-9b6d6427ea5b

import Definitions.Def_mme_CW_2376_hash_incidence_universes
import Theorems.Thm_mme_CW_2376_target_address_hash_parameter_card
import Theorems.Thm_mme_CW_2376_augmented_pair_collision_card_le
import Theorems.Thm_mme_finset_incidence_double_count

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000

/-- Exact aggregate target survival and an aggregate collision bound over all
augmented affine hash states. -/
theorem solution
    (m p : ℕ) (hm : 0 < m) [Fact p.Prime]
    (hp5 : 5 ≤ p) (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2)) :
    (∑ q ∈ cw2376AugmentedHashStateUniverse m p,
        (cw2376ExactTargetEdges
          (cw2376RetainedEdgesAtAugmentedState m p S q)).card) =
        (cw2376AllExactTargetEdges m).card * S.card *
          p ^ cw2376ProfileLength m ∧
      (∑ q ∈ cw2376AugmentedHashStateUniverse m p,
        (cw2376TargetAmbientCollisions
          (cw2376RetainedEdgesAtAugmentedState m p S q)).card) ≤
        (cw2376AllTargetAmbientCollisions m).card *
          p ^ cw2376ProfileLength m := by
  classical
  let Ω := cw2376AugmentedHashStateUniverse m p
  let T := cw2376AllExactTargetEdges m
  let C := cw2376AllTargetAmbientCollisions m
  let E := cw2376RetainedEdgesAtAugmentedState m p S
  have hEsubset (q) : E q ⊆ cw2376MarginalSupportedUniverse m := by
    intro a ha
    simp only [cw2376MarginalSupportedUniverse, Finset.mem_univ]
  have htarget (q) :
      cw2376ExactTargetEdges (E q) =
        T.filter (fun a => a ∈ E q) := by
    ext a
    simp only [T, cw2376AllExactTargetEdges,
      cw2376ExactTargetEdges, Finset.mem_filter]
    constructor
    · rintro ⟨haE, haTarget⟩
      exact ⟨⟨hEsubset q haE, haTarget⟩, haE⟩
    · rintro ⟨⟨haU, haTarget⟩, haE⟩
      exact ⟨haE, haTarget⟩
  have hcollision (q) :
      cw2376TargetAmbientCollisions (E q) =
        C.filter (fun ab => ab.1 ∈ E q ∧ ab.2 ∈ E q) := by
    ext ab
    simp only [C, cw2376AllTargetAmbientCollisions,
      cw2376TargetAmbientCollisions,
      cw2376ExactTargetEdges, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨haE, haTarget⟩, hbE⟩, hne, hi⟩
      exact ⟨⟨⟨⟨hEsubset q haE, haTarget⟩, hEsubset q hbE⟩,
        hne, hi⟩, haE, hbE⟩
    · rintro ⟨⟨⟨⟨haU, haTarget⟩, hbU⟩, hne, hi⟩, haE, hbE⟩
      exact ⟨⟨⟨haE, haTarget⟩, hbE⟩, hne, hi⟩
  have hstate (a : CW2376MarginalSupportedAddress m) :
      Ω.filter (fun q => a ∈ E q) =
        cw2376AugmentedHashStatesRetainingAddress m p S a := by
    ext q
    simp only [Ω, E, cw2376AugmentedHashStateUniverse,
      cw2376RetainedEdgesAtAugmentedState,
      cw2376AugmentedHashStatesRetainingAddress,
      Finset.mem_filter, Finset.mem_univ, true_and]
  have hpairstate
      (ab : CW2376MarginalSupportedAddress m ×
        CW2376MarginalSupportedAddress m) :
      Ω.filter (fun q => ab.1 ∈ E q ∧ ab.2 ∈ E q) =
        cw2376AugmentedHashStatesRetainingAddress m p S ab.1 ∩
          cw2376AugmentedHashStatesRetainingAddress m p S ab.2 := by
    ext q
    simp only [Ω, E, cw2376AugmentedHashStateUniverse,
      cw2376RetainedEdgesAtAugmentedState,
      cw2376AugmentedHashStatesRetainingAddress,
      Finset.mem_filter, Finset.mem_inter, Finset.mem_univ, true_and]
  constructor
  · change (∑ q ∈ Ω, (cw2376ExactTargetEdges (E q)).card) =
      T.card * S.card * p ^ cw2376ProfileLength m
    calc
      (∑ q ∈ Ω, (cw2376ExactTargetEdges (E q)).card) =
          ∑ q ∈ Ω, (T.filter (fun a => a ∈ E q)).card := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [htarget]
      _ = ∑ a ∈ T, (Ω.filter (fun q => a ∈ E q)).card :=
        mme_finset_incidence_double_count Ω T
          (fun q a => a ∈ E q)
      _ = ∑ a ∈ T, S.card * p ^ cw2376ProfileLength m := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hstate]
        exact mme_CW_2376_target_address_hash_parameter_card
          m p hm hpodd S hSrange a
      _ = T.card * S.card * p ^ cw2376ProfileLength m := by
        simp [mul_assoc]
  · change (∑ q ∈ Ω,
      (cw2376TargetAmbientCollisions (E q)).card) ≤
        C.card * p ^ cw2376ProfileLength m
    calc
      (∑ q ∈ Ω, (cw2376TargetAmbientCollisions (E q)).card) =
          ∑ q ∈ Ω,
            (C.filter (fun ab => ab.1 ∈ E q ∧ ab.2 ∈ E q)).card := by
              apply Finset.sum_congr rfl
              intro q hq
              rw [hcollision]
      _ = ∑ ab ∈ C,
          (Ω.filter (fun q => ab.1 ∈ E q ∧ ab.2 ∈ E q)).card :=
        mme_finset_incidence_double_count Ω C
          (fun q ab => ab.1 ∈ E q ∧ ab.2 ∈ E q)
      _ ≤ ∑ ab ∈ C, p ^ cw2376ProfileLength m := by
        apply Finset.sum_le_sum
        intro ab habC
        rw [hpairstate]
        have habData : ab.1 ≠ ab.2 ∧
            ∃ i : Fin 3, ab.1.1 i = ab.2.1 i := by
          have hfull := habC
          simp only [C, cw2376AllTargetAmbientCollisions,
            cw2376TargetAmbientCollisions, Finset.mem_filter,
            Finset.mem_product] at hfull
          exact hfull.2
        obtain ⟨hne, i, hi⟩ := habData
        exact mme_CW_2376_augmented_pair_collision_card_le
          m p hp5 hpodd S ab.1 ab.2 hne i hi
      _ = C.card * p ^ cw2376ProfileLength m := by simp
