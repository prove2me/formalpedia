-- Prove2me | solution 1 for Catalog.Novelty.FriendshipChromaticPolynomial.pairColors_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:40:27.372391+00:00
-- url     : https://prove2.me/submissions/1bdabbca-7667-45cc-9242-6005adea8496

-- Sol generated from Geometry/FriendshipChromaticPolynomial.lean
import Mathlib
import Definitions.Def_Geometry_FriendshipChromaticPolynomial
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Chromatic Polynomial of the Friendship (Windmill) Graph

This file computes, in closed form, the *chromatic counting function* of the **friendship graph**
`F_n` (also called the windmill graph, or Dutch windmill).  The friendship graph consists of a
single central person who is friends with everyone, together with `n` disjoint pairs of people, each
pair being mutual friends: geometrically, `n` triangles all sharing one common vertex.

In the "emotions" reading of graph coloring (assign each person one of `q` emotions so that no two
friends share the same emotion), `chromVal n q` counts the number of consistent emotion assignments
of `F_n` with a palette of `q` emotions.  This is the value `P(F_n, q)` of the chromatic polynomial.

## Main result

* `chromVal_friendship` :  `P(F_n, q) = q · ((q-1)(q-2))^n`.

  The central person picks any of `q` emotions; then, independently for each of the `n` triangles,
  the two outer people must both differ from the centre and from each other, giving `(q-1)(q-2)`
  admissible pairs per triangle.

## Consequences

* `friendship_chromVal_six`     :  with the six basic emotions, `P(F_n, 6) = 6 · 20^n` — this is the
                                   original "graph coloring with emotions" conjecture, now proved.
* `chromVal_pos_iff_colorable`  :  the counting function detects colorability.
* `friendship_colorable_three`  :  three emotions always suffice.
* `friendship_colorable_six`    :  the six basic emotions always suffice.
* `friendship_not_colorable_two`:  for `n ≥ 1`, two emotions never suffice (each triangle is a
                                   clique of size three).
* `friendship_chromaticNumber`  :  for `n ≥ 1`, the chromatic number of `F_n` is exactly `3`; hence,
                                   restricted to the emotional regime `k ≥ 3`, its emotional
                                   chromatic number is `3` and lies in the six-emotion window `[3,6]`.

The proof of the closed form is a genuine bijective count: proper colorings of `F_n` are put in
explicit bijection with a choice of centre colour together with, per triangle, an ordered pair of
colours avoiding the centre and each other (`frEquiv`), whose count is `(q-1)(q-2)` (`pairColors_card`).

The file is self-contained: it imports only Mathlib and redevelops the small amount of
chromatic-counting API it needs.
-/


open Catalog.Novelty.FriendshipChromaticPolynomial

open SimpleGraph Finset

/-! ## The friendship graph -/






/-! ## Counting the colourings of one triangle -/

/-- For fixed centre colour `z` and one already-chosen outer colour `a ≠ z`, the remaining outer
colour has exactly `q - 2` choices (it must avoid both `z` and `a`). -/
theorem fiber_card (q : ℕ) (z a : Fin q) (h : a ≠ z) :
    Fintype.card {b : Fin q // b ≠ z ∧ b ≠ a} = q - 2 := by
  rw [Fintype.card_subtype]
  have heq : (univ.filter (fun b : Fin q => b ≠ z ∧ b ≠ a)) = ({z, a} : Finset (Fin q))ᶜ := by
    ext b; simp
  rw [heq, Finset.card_compl, Fintype.card_fin, Finset.card_pair h.symm]


/-! ## The colouring bijection -/


/-! ## The chromatic polynomial of the friendship graph -/


/-! ## Consequences -/








open Catalog.Novelty.FriendshipChromaticPolynomial in
theorem solution(q : ℕ) (z : Fin q) :
    Fintype.card {p : Fin q × Fin q // p.1 ≠ z ∧ p.2 ≠ z ∧ p.1 ≠ p.2} = (q - 1) * (q - 2) := by
  have e : {p : Fin q × Fin q // p.1 ≠ z ∧ p.2 ≠ z ∧ p.1 ≠ p.2}
      ≃ Σ a : {a : Fin q // a ≠ z}, {b : Fin q // b ≠ z ∧ b ≠ a.1} :=
    { toFun := fun p => ⟨⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2.1, fun hh => p.2.2.2 hh.symm⟩⟩
      invFun := fun s => ⟨(s.1.1, s.2.1), s.1.2, s.2.2.1, fun hh => s.2.2.2 hh.symm⟩
      left_inv := by rintro ⟨⟨a, b⟩, -⟩; rfl
      right_inv := by rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  rw [Finset.sum_congr rfl (fun a _ => fiber_card q z a.1 a.2)]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hz : Fintype.card {a : Fin q // a ≠ z} = q - 1 := by
    rw [Fintype.card_subtype]
    have : (univ.filter (fun a : Fin q => a ≠ z)) = ({z} : Finset (Fin q))ᶜ := by ext a; simp
    rw [this, Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
  rw [hz]
