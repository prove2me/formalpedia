-- Prove2me | solution 1 for KnownUnresolvedCards.sum_fiber2_row
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T20:27:52.218863+00:00
-- url     : https://prove2.me/submissions/ba1a1362-ecfd-4a95-bb8c-86663737832a

import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_PermCount

open KnownUnresolvedCards
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

@[simp] lemma mem_fiber {i a : α} {σ : Equiv.Perm α} : σ ∈ fiber i a ↔ σ i = a := by
  simp [fiber]

@[simp] lemma mem_fiber₂ {i j a b : α} {σ : Equiv.Perm α} :
    σ ∈ fiber₂ i j a b ↔ σ i = a ∧ σ j = b := by
  simp [fiber₂]


lemma fiber₂_diag (i a : α) : fiber₂ i i a a = fiber i a := by
  ext σ; simp


lemma fiber₂_eq_empty_of_ne {i j : α} (hij : i ≠ j) (a : α) : fiber₂ i j a a = ∅ := by
  ext σ
  simp only [mem_fiber₂, Finset.notMem_empty, iff_false, not_and]
  intro h1 h2
  exact hij (σ.injective (h1.trans h2.symm))

/-! ## Transposition symmetry -/


lemma card_fiber₂_eq (i j a b b' : α) (hb : a ≠ b) (hb' : a ≠ b') :
    (fiber₂ i j a b).card = (fiber₂ i j a b').card := by
  refine Finset.card_nbij' (fun σ => Equiv.swap b b' * σ) (fun σ => Equiv.swap b b' * σ)
    ?_ ?_ ?_ ?_
  · intro σ hσ
    have h : σ i = a ∧ σ j = b := by simpa using hσ
    refine Finset.mem_coe.mpr (mem_fiber₂.mpr ⟨?_, ?_⟩)
    · simp [Equiv.Perm.mul_apply, h.1, Equiv.swap_apply_of_ne_of_ne hb hb']
    · simp [Equiv.Perm.mul_apply, h.2]
  · intro σ hσ
    have h : σ i = a ∧ σ j = b' := by simpa using hσ
    refine Finset.mem_coe.mpr (mem_fiber₂.mpr ⟨?_, ?_⟩)
    · simp [Equiv.Perm.mul_apply, h.1, Equiv.swap_apply_of_ne_of_ne hb hb']
    · simp [Equiv.Perm.mul_apply, h.2]
  · intro σ _
    simp [← mul_assoc, Equiv.swap_mul_self]
  · intro σ _
    simp [← mul_assoc, Equiv.swap_mul_self]


lemma sum_card_fiber (i : α) : ∑ a, (fiber i a).card = Fintype.card (Equiv.Perm α) := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun σ : Equiv.Perm α => σ i) (s := (univ : Finset (Equiv.Perm α)))
    (t := (univ : Finset α)) (fun σ _ => mem_univ _)
  rw [Finset.card_univ] at h
  rw [h]
  exact Finset.sum_congr rfl fun a _ => by rw [fiber]


lemma sum_card_fiber₂ (i j : α) (a : α) :
    ∑ b, (fiber₂ i j a b).card = (fiber i a).card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun σ : Equiv.Perm α => σ j) (s := fiber i a)
    (t := (univ : Finset α)) (fun σ _ => mem_univ _)
  rw [h]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ext σ
  simp


theorem card_fiber₂_mul {i j a b : α} (hij : i ≠ j) (hab : a ≠ b) :
    (Fintype.card α - 1) * (fiber₂ i j a b).card = (fiber i a).card := by
  classical
  rw [← sum_card_fiber₂ i j a]
  rw [← Finset.sum_erase_add (univ : Finset α) _ (mem_univ a)]
  rw [fiber₂_eq_empty_of_ne hij a]
  simp only [Finset.card_empty, add_zero]
  rw [Finset.sum_congr rfl
    (fun b' (hb' : b' ∈ (univ : Finset α).erase a) =>
      card_fiber₂_eq i j a b' b (Ne.symm (Finset.mem_erase.mp hb').1) hab)]
  rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (mem_univ a), Finset.card_univ]

/-! ## The score of a strategy -/


theorem solution (g : α → α) (i : α) :
    (Fintype.card α - 1) * ∑ j, (fiber₂ i j (g i) (g j)).card
      = ((Fintype.card α - 1) + distinctCalls g i) * (fiber i (g i)).card := by
  classical
  rw [← Finset.sum_erase_add (univ : Finset α) _ (mem_univ i), fiber₂_diag, Nat.mul_add]
  have hoff : (Fintype.card α - 1) * ∑ j ∈ (univ : Finset α).erase i,
      (fiber₂ i j (g i) (g j)).card = distinctCalls g i * (fiber i (g i)).card := by
    rw [Finset.mul_sum]
    have hterm : ∀ j ∈ (univ : Finset α).erase i,
        (Fintype.card α - 1) * (fiber₂ i j (g i) (g j)).card
          = if g i ≠ g j then (fiber i (g i)).card else 0 := by
      intro j hj
      have hij : i ≠ j := (Ne.symm (Finset.mem_erase.mp hj).1)
      by_cases hgc : g i = g j
      · rw [if_neg (by simpa using hgc), hgc, fiber₂_eq_empty_of_ne hij (g j)]
        simp
      · rw [if_pos hgc, card_fiber₂_mul hij hgc]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
      add_zero, smul_eq_mul]
    congr 1
    rw [distinctCalls]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase, mem_univ, and_true, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨fun hji => h (by rw [hji]), h⟩
  rw [hoff]
  ring

