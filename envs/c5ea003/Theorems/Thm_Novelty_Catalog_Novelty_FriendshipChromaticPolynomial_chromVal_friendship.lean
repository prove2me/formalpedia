-- Prove2me | Theorems.Thm_Novelty_Catalog_Novelty_FriendshipChromaticPolynomial_chromVal_friendship
-- name    : Novelty.Catalog.Novelty.FriendshipChromaticPolynomial.chromVal_friendship
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-18T00:19:59.308638+00:00
-- url     : https://prove2.me/theorems/c0af91e4-da3a-4117-8b68-f54c51ba980f
-- title:
--   Main theorem.
-- statement:
--   **Main theorem.** The chromatic polynomial of the friendship graph `F_n` evaluated at `q` is
--   `q · ((q-1)(q-2))^n`: pick any of `q` emotions for the central person, then independently choose,
--   for each of the `n` triangles, an ordered pair of outer emotions both different from the centre and
--   from each other — `(q-1)(q-2)` choices per triangle.
--
--   ```lean
--   theorem Catalog.Novelty.FriendshipChromaticPolynomial.chromVal_friendship(n q : ℕ) :
--       chromVal n q = q * ((q - 1) * (q - 2)) ^ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/FriendshipChromaticPolynomial.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/FriendshipChromaticPolynomial.lean#L156

-- Thm stub generated from Novelty/FriendshipChromaticPolynomial.lean
import Mathlib
import Definitions.Def_Novelty_FriendshipChromaticPolynomial
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

theorem Novelty.Catalog.Novelty.FriendshipChromaticPolynomial.chromVal_friendship(n q : ℕ) :
    chromVal n q = q * ((q - 1) * (q - 2)) ^ n := by sorry
