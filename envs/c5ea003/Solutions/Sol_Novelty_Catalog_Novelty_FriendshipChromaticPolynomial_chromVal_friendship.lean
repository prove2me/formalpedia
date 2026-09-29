-- Prove2me | solution 1 for Novelty.Catalog.Novelty.FriendshipChromaticPolynomial.chromVal_friendship
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-19T17:23:57.788698+00:00
-- url     : https://prove2.me/submissions/45ef02f7-5d88-4523-9628-011aadf0f394

import Mathlib
import Definitions.Def_Novelty_FriendshipChromaticPolynomial

open Catalog.Novelty.FriendshipChromaticPolynomial
open Finset

/-- For fixed centre colour `z` and one already-chosen outer colour `a ≠ z`, the remaining outer
colour has exactly `q - 2` choices. -/
private theorem fiber_card (q : ℕ) (z a : Fin q) (h : a ≠ z) :
    Fintype.card {b : Fin q // b ≠ z ∧ b ≠ a} = q - 2 := by
  rw [Fintype.card_subtype]
  have heq : univ.filter (fun b : Fin q => b ≠ z ∧ b ≠ a) = ({z, a} : Finset (Fin q))ᶜ := by
    ext b; simp
  rw [heq, card_compl, Fintype.card_fin, card_pair h.symm]

/-- Ordered pairs of colours both avoiding `z` and each other. -/
private theorem pairColors_card (q : ℕ) (z : Fin q) :
    Fintype.card {p : Fin q × Fin q // p.1 ≠ z ∧ p.2 ≠ z ∧ p.1 ≠ p.2} =
      (q - 1) * (q - 2) := by
  have e : {p : Fin q × Fin q // p.1 ≠ z ∧ p.2 ≠ z ∧ p.1 ≠ p.2}
      ≃ Σ a : {a : Fin q // a ≠ z}, {b : Fin q // b ≠ z ∧ b ≠ a.1} :=
    { toFun := fun p => ⟨⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2.1, fun hh => p.2.2.2 hh.symm⟩⟩
      invFun := fun s => ⟨(s.1.1, s.2.1), s.1.2, s.2.2.1, fun hh => s.2.2.2 hh.symm⟩
      left_inv := by rintro ⟨⟨a, b⟩, -⟩; rfl
      right_inv := by rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  rw [sum_congr rfl (fun a _ => fiber_card q z a.1 a.2)]
  rw [sum_const, card_univ, smul_eq_mul]
  have hz : Fintype.card {a : Fin q // a ≠ z} = q - 1 := by
    rw [Fintype.card_subtype]
    have : univ.filter (fun a : Fin q => a ≠ z) = ({z} : Finset (Fin q))ᶜ := by
      ext a; simp
    rw [this, card_compl, Fintype.card_fin, card_singleton]
  rw [hz]

theorem solution (n q : ℕ) :
    chromVal n q = q * ((q - 1) * (q - 2)) ^ n := by
  unfold chromVal
  rw [← Fintype.card_subtype, Fintype.card_congr (frEquiv n q), Fintype.card_sigma]
  have hcard : ∀ z : Fin q,
      Fintype.card (Fin n → {p : Fin q × Fin q // p.1 ≠ z ∧ p.2 ≠ z ∧ p.1 ≠ p.2}) =
        ((q - 1) * (q - 2)) ^ n := by
    intro z; rw [Fintype.card_fun, pairColors_card, Fintype.card_fin]
  rw [sum_congr rfl (fun z _ => hcard z), sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
