-- Prove2me | solution 1 for mme_CW_2376_collision_universe_card_of_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:15:28.050739+00:00
-- url     : https://prove2.me/submissions/8f45d9b5-8cc0-4a19-8b42-6b2123fafbb1

import Definitions.Def_mme_CW_2376_hash_incidence_universes

open MME BigOperators

set_option autoImplicit false

/-- A uniform per-mode ambient completion-degree bound gives the factor-three
bound for all directed target-to-ambient collisions. -/
theorem solution
    (m D : ℕ)
    (hdeg : ∀ i : Fin 3, ∀ a ∈ cw2376AllExactTargetEdges m,
      ((cw2376MarginalSupportedUniverse m).filter
        (fun b => b.1 i = a.1 i)).card ≤ D) :
    (cw2376AllTargetAmbientCollisions m).card ≤
      3 * (cw2376AllExactTargetEdges m).card * D := by
  classical
  let U := cw2376MarginalSupportedUniverse m
  let T := cw2376AllExactTargetEdges m
  let C := cw2376AllTargetAmbientCollisions m
  let star (i : Fin 3) (a : CW2376MarginalSupportedAddress m) :=
    U.filter (fun b => b.1 i = a.1 i)
  let Ci (i : Fin 3) := T.biUnion (fun a =>
    (star i a).image (fun b => (a, b)))
  let CU := (Finset.univ : Finset (Fin 3)).biUnion Ci
  have hsubset : C ⊆ CU := by
    intro ab hab
    have hfull := hab
    simp only [C, cw2376AllTargetAmbientCollisions,
      cw2376TargetAmbientCollisions, Finset.mem_filter,
      Finset.mem_product] at hfull
    obtain ⟨⟨haT, hbU⟩, hne, i, hi⟩ := hfull
    simp only [CU, Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨i, ?_⟩
    simp only [Ci, Finset.mem_biUnion]
    refine ⟨ab.1, haT, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨ab.2, ?_, rfl⟩
    simp only [star, Finset.mem_filter]
    exact ⟨hbU, hi.symm⟩
  calc
    C.card ≤ CU.card := Finset.card_le_card hsubset
    _ ≤ ∑ i : Fin 3, (Ci i).card := by
      simpa only [CU]
        using (Finset.card_biUnion_le :
          CU.card ≤ ∑ i ∈ (Finset.univ : Finset (Fin 3)), (Ci i).card)
    _ ≤ ∑ i : Fin 3, ∑ a ∈ T, (star i a).card := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        (Ci i).card ≤ ∑ a ∈ T,
            ((star i a).image (fun b => (a, b))).card := by
          simpa only [Ci] using (Finset.card_biUnion_le :
            (T.biUnion (fun a =>
              (star i a).image (fun b => (a, b)))).card ≤
              ∑ a ∈ T, ((star i a).image (fun b => (a, b))).card)
        _ ≤ ∑ a ∈ T, (star i a).card := by
          apply Finset.sum_le_sum
          intro a ha
          exact Finset.card_image_le
    _ ≤ ∑ i : Fin 3, ∑ a ∈ T, D := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro a ha
      exact hdeg i a ha
    _ = 3 * T.card * D := by simp [mul_assoc]
