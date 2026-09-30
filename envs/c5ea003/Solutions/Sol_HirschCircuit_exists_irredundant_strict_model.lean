-- Prove2me | solution 1 for HirschCircuit.exists_irredundant_strict_model
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-08T16:16:52.943661+00:00
-- url     : https://prove2.me/submissions/2337fc4e-5ad3-4804-a407-b8675ee72d8b

import Definitions.Def_Hirsch_circuit_model
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped RealInnerProductSpace
open Hirsch

theorem solution
    (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b) (hv : v ∈ Hpoly a b)
    (hsep : ∀ j, a j ≠ 0 → ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) :
    ∃ m : ℕ, m ≤ n ∧ ∃ e : Fin m ↪ Fin n,
      Hpoly (fun j => a (e j)) (fun j => b (e j)) = Hpoly a b ∧
      RowPresentationIrredundant (fun j => a (e j)) (fun j => b (e j)) ∧
      StrictlyFeasibleRows (fun j => a (e j)) (fun j => b (e j)) := by
  classical
  let Good : Finset (Fin n) → Prop := fun S =>
    ∀ x : EuclideanSpace ℝ (Fin d),
      (∀ i ∈ S, ⟪a i, x⟫ ≤ b i) → x ∈ Hpoly a b
  have hall : Good Finset.univ := by
    intro x hx i
    exact hx i (Finset.mem_univ i)
  have hex : ∃ k : ℕ, ∃ S : Finset (Fin n), S.card = k ∧ Good S :=
    ⟨n, Finset.univ, by simp, hall⟩
  obtain ⟨S, hScard, hGood⟩ := Nat.find_spec hex
  have hmin : ∀ T : Finset (Fin n), Good T → S.card ≤ T.card := by
    intro T hT
    rw [hScard]
    exact Nat.find_min' hex ⟨T, rfl, hT⟩
  have hessential : ∀ i ∈ S, ∃ x : EuclideanSpace ℝ (Fin d),
      (∀ j ∈ S, j ≠ i → ⟪a j, x⟫ ≤ b j) ∧ b i < ⟪a i, x⟫ := by
    intro i hi
    by_contra hn
    have hrem : Good (S.erase i) := by
      intro x hx
      have hix : ⟪a i, x⟫ ≤ b i := by
        by_contra hnot
        apply hn
        refine ⟨x, ?_, lt_of_not_ge hnot⟩
        intro j hj hji
        exact hx j (Finset.mem_erase.mpr ⟨hji, hj⟩)
      apply hGood x
      intro j hj
      by_cases hji : j = i
      · simpa only [hji] using hix
      · exact hx j (Finset.mem_erase.mpr ⟨hji, hj⟩)
    have hcard := hmin (S.erase i) hrem
    have hlt : (S.erase i).card < S.card := Finset.card_erase_lt_of_mem hi
    omega
  let m : ℕ := Fintype.card S
  let E : Fin m ≃ S := (Fintype.equivFin S).symm
  let e : Fin m ↪ Fin n :=
    { toFun := fun j => (E j).val
      inj' := by
        intro j k h
        exact E.injective (Subtype.ext h) }
  have hemem : ∀ j : Fin m, e j ∈ S := fun j => (E j).property
  have hesurj : ∀ i ∈ S, ∃ j : Fin m, e j = i := by
    intro i hi
    refine ⟨E.symm ⟨i, hi⟩, ?_⟩
    change (E (E.symm ⟨i, hi⟩)).val = i
    rw [E.apply_symm_apply]
  have hmn : m ≤ n := by
    have hc := Finset.card_le_card (Finset.subset_univ S)
    simpa only [Finset.card_univ, Fintype.card_fin, m, Fintype.card_coe] using hc
  have hP : Hpoly (fun j => a (e j)) (fun j => b (e j)) = Hpoly a b := by
    ext x
    constructor
    · intro hx
      apply hGood x
      intro i hi
      obtain ⟨j, hj⟩ := hesurj i hi
      simpa only [hj] using hx j
    · intro hx j
      exact hx (e j)
  have hirr : RowPresentationIrredundant (fun j => a (e j)) (fun j => b (e j)) := by
    intro i
    obtain ⟨x, hx, hxi⟩ := hessential (e i) (hemem i)
    refine ⟨x, ?_, hxi⟩
    intro j hji
    exact hx (e j) (hemem j) (fun h => hji (e.injective h))
  have hnonzero : ∀ j : Fin m, a (e j) ≠ 0 := by
    intro j hj0
    obtain ⟨x, _, hx⟩ := hirr j
    change b (e j) < ⟪a (e j), x⟫ at hx
    have hj := hu (e j)
    rw [hj0, inner_zero_left] at hx hj
    linarith
  refine ⟨m, hmn, e, hP, hirr, ?_⟩
  refine ⟨(1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v, ?_⟩
  intro j
  have hju := hu (e j)
  have hjv := hv (e j)
  have hcombo :
      ⟪a (e j), (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v⟫ =
        (⟪a (e j), u⟫ + ⟪a (e j), v⟫) / 2 := by
    simp only [inner_add_right, inner_smul_right]
    ring
  rw [hcombo]
  rcases hsep (e j) (hnonzero j) with hnu | hnv
  · have hlt : ⟪a (e j), u⟫ < b (e j) := lt_of_le_of_ne hju hnu
    linarith
  · have hlt : ⟪a (e j), v⟫ < b (e j) := lt_of_le_of_ne hjv hnv
    linarith

#print axioms solution
