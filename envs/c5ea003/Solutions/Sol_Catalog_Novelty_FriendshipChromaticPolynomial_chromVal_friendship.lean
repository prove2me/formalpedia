-- Prove2me | solution 1 for Catalog.Novelty.FriendshipChromaticPolynomial.chromVal_friendship
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:42:47.42041+00:00
-- url     : https://prove2.me/submissions/8e9fe000-b2fa-441b-98a6-2e65691e0fb2

-- Sol generated from Geometry/FriendshipChromaticPolynomial.lean
import Mathlib
import Definitions.Def_Geometry_FriendshipChromaticPolynomial
import Theorems.Thm_Catalog_Novelty_FriendshipChromaticPolynomial_pairColors_card
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



/-! ## The colouring bijection -/


/-! ## The chromatic polynomial of the friendship graph -/


/-! ## Consequences -/








open Catalog.Novelty.FriendshipChromaticPolynomial in
theorem solution(n q : ℕ) :
    chromVal n q = q * ((q - 1) * (q - 2)) ^ n := by
  unfold chromVal
  rw [← Fintype.card_subtype, Fintype.card_congr (frEquiv n q), Fintype.card_sigma]
  have hcard : ∀ z : Fin q,
      Fintype.card (Fin n → {p : Fin q × Fin q // p.1 ≠ z ∧ p.2 ≠ z ∧ p.1 ≠ p.2})
        = ((q - 1) * (q - 2)) ^ n := by
    intro z; rw [Fintype.card_fun, pairColors_card, Fintype.card_fin]
  rw [Finset.sum_congr rfl (fun z _ => hcard z), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
