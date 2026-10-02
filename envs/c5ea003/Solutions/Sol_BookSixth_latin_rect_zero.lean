-- Prove2me | solution 1 for BookSixth.latin_rect_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T04:04:51.726952+00:00
-- url     : https://prove2.me/submissions/297202de-3034-4830-baff-596b6586c536

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (n : ℕ) :
    (Finset.univ.filter (fun R : Fin 0 → Fin n → Fin n =>
      (∀ i, Function.Bijective (R i)) ∧ (∀ j, Function.Injective (fun i => R i j)))).card
    = 1 := by
  classical
  have hall : ∀ R ∈ (Finset.univ : Finset (Fin 0 → Fin n → Fin n)),
      (∀ i, Function.Bijective (R i)) ∧ (∀ j, Function.Injective (fun i => R i j)) := by
    intro R _
    refine ⟨fun i => i.elim0, fun j => ?_⟩
    intro a b _
    exact a.elim0
  rw [Finset.filter_true_of_mem hall, Finset.card_univ]
  exact Fintype.card_ofSubsingleton _
