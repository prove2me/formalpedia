-- Prove2me | solution 1 for BookSixth.latin_rect_full
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T04:51:26.918476+00:00
-- url     : https://prove2.me/submissions/194f904d-ba58-47c7-a389-b8063acf7f75

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (n : ℕ) :
    (Finset.univ.filter (fun R : Fin n → Fin n → Fin n =>
      (∀ i, Function.Bijective (R i)) ∧ (∀ j, Function.Injective (fun i => R i j)))).card
    = latinCount n := by
  classical
  have hsurj : ∀ f : Fin n → Fin n, Function.Injective f → Function.Surjective f := by
    intro f hinj b
    have h1 : (Finset.univ.image f).card = Fintype.card (Fin n) := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    have h2 : Finset.univ.image f = Finset.univ := Finset.eq_univ_of_card _ h1
    have hb : b ∈ Finset.univ.image f := h2.symm ▸ Finset.mem_univ b
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨a, rfl⟩
  have heq : (Finset.univ.filter (fun R : Fin n → Fin n → Fin n =>
      (∀ i, Function.Bijective (R i)) ∧ (∀ j, Function.Injective (fun i => R i j))))
      = Finset.univ.filter (fun L : Fin n → Fin n → Fin n => Latin L) := by
    apply Finset.filter_congr
    intro L _
    simp only [BookSixth.Latin]
    constructor
    · intro h
      exact ⟨h.1, fun j => ⟨h.2 j, hsurj _ (h.2 j)⟩⟩
    · intro h
      exact ⟨h.1, fun j => (h.2 j).1⟩
  rw [heq]
  rfl
