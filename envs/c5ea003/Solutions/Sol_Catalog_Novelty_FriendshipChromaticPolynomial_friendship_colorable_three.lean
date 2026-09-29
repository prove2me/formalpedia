-- Prove2me | solution 1 for Catalog.Novelty.FriendshipChromaticPolynomial.friendship_colorable_three
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:46:45.712978+00:00
-- url     : https://prove2.me/submissions/55500e5b-a6a4-4fde-8303-e1f81f454a44

-- Sol generated from Geometry/FriendshipChromaticPolynomial.lean
import Mathlib
import Definitions.Def_Geometry_FriendshipChromaticPolynomial
import Theorems.Thm_Catalog_Novelty_FriendshipChromaticPolynomial_chromVal_friendship
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


/-- **The counting function is a colorability oracle.**  There is at least one consistent emotion
assignment with `q` emotions iff `P(F_n, q) > 0`. -/
theorem chromVal_pos_iff_colorable (n q : ℕ) :
    0 < chromVal n q ↔ (friendship n).Colorable q := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Finset.card_pos.mp h
    exact ⟨SimpleGraph.Coloring.mk c (fun {x y} hxy => (Finset.mem_filter.mp hc).2 x y hxy)⟩
  · rintro ⟨c⟩
    exact Finset.card_pos.mpr
      ⟨c.toFun, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x y hxy => c.valid hxy⟩⟩






open Catalog.Novelty.FriendshipChromaticPolynomial in
theorem solution(n : ℕ) : (friendship n).Colorable 3 := by
  rw [← chromVal_pos_iff_colorable, chromVal_friendship]; norm_num
