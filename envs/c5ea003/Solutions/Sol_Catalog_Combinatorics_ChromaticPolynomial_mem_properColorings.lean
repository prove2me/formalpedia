-- Prove2me | solution 1 for Catalog.Combinatorics.ChromaticPolynomial.mem_properColorings
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:49:50.73619+00:00
-- url     : https://prove2.me/submissions/958d392a-eb4b-41a6-b3e5-3063a7d590d7

-- Sol generated from Geometry/ChromaticPolynomial.lean
import Mathlib
import Definitions.Def_Geometry_ChromaticPolynomial
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chromatic Polynomials and Deletion–Contraction

This file develops the *chromatic counting function* of a finite simple graph: for `q : ℕ`,
`chromVal G q` is the number of proper colorings `V → Fin q` of `G`.  This is the value at `q`
of the chromatic polynomial `P(G, q)`.

Mathlib provides `SimpleGraph.Coloring`, `SimpleGraph.Colorable`, and `SimpleGraph.chromaticNumber`,
but it does **not** provide the chromatic polynomial, the deletion–contraction recurrence, or the
closed-form evaluations for the empty and complete graphs.  We fill these gaps:

  * `chromVal_bot`     :  `P(Ē_n, q) = q ^ n`            (the empty graph),
  * `chromVal_top`     :  `P(K_n, q) = q^{\underline n}` (the complete graph, falling factorial),
  * `deletion_contraction` :
        `P(G − e, q) = P(G, q) + P(G / e, q)`
    for every edge `e = {a,b}` of `G`, where `G − e` deletes `e` and `G / e` contracts it.

The deletion–contraction recurrence is the structural engine behind the entire theory of
chromatic polynomials (e.g. Whitney's broken-circuit theorem and the fact that `P(G,·)` is a
polynomial with alternating-sign integer coefficients).

-- !-- Lab Notes -- !--
HYPOTHESIS.  Counting proper colorings should satisfy `P(G−e) = P(G) + P(G/e)`: a proper coloring of
`G−e` either gives the endpoints of `e` distinct colors (these are exactly the proper colorings of
`G`) or equal colors (these are exactly the proper colorings of the contraction `G/e`).

EXPERIMENTAL PLAN.
  (1) Define `delEdge G a b` (delete the single edge `{a,b}`) and `contract G a b` (merge `b` into
      `a`, on the vertex set `{v // v ≠ b}`), both as honest `SimpleGraph`s with decidable adjacency.
  (2) Show `{proper colorings of G−e with `c a ≠ c b`} = {proper colorings of G}` as finsets.
  (3) Build an explicit bijection `{proper colorings of G−e with `c a = c b`} ≃ {proper colorings
      of G/e}` by restriction/extension along `{v // v ≠ b} ↪ V`.
  (4) Split `P(G−e)` by the decidable predicate `c a = c b` and assemble (2)+(3).

INSIGHT.  Modeling the contraction on the subtype `{v // v ≠ b}` (rather than a quotient) keeps
adjacency decidable and makes the coloring bijection a concrete restrict/extend pair, avoiding all
quotient bookkeeping.  The merged vertex's incidences are encoded by redirecting `b`'s neighbors to
`a` in `contract`'s adjacency relation.
-- !-- End Lab Notes -- !--
-/


open Catalog.Combinatorics.ChromaticPolynomial

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Proper colorings as a finset of functions -/




/-! ## Edge deletion and contraction as honest graphs -/





/-! ## Evaluations on the empty and complete graphs -/

/-
**Empty graph.** `P(Ē_n, q) = q ^ n`: every function is a proper coloring of the edgeless
graph.
-/

/-
**Complete graph.** `P(K_n, q) = q^{\underline n}` (the falling factorial): the proper
colorings of the complete graph are exactly the injective functions `V → Fin q`.
-/

/-! ## Deletion–contraction -/

variable {α : Type*} [Fintype α] [DecidableEq α]

/-
The proper colorings of `G − e` that give the endpoints of `e` *distinct* colors are exactly
the proper colorings of `G`.
-/

/-
The proper colorings of `G − e` that give the endpoints of `e` *equal* colors are in bijection
with the proper colorings of the contraction `G / e`; hence the cardinalities agree.
-/

/-
**Deletion–contraction for the chromatic polynomial.**
For every edge `e = {a, b}` of `G`,
`P(G − e, ·) = P(G, ·) + P(G / e, ·)` (counted with `α` colors).
-/

/-
The same recurrence specialized to the chromatic counting function with `q` colors.
-/

/-
-- !-- Lab Notes (synthesis & critique) -- !--
OUTCOMES.
  * `chromVal_bot` / `chromVal_top`: the edgeless graph gives `q^n` (all functions proper) and the
    complete graph gives the falling factorial `q^{\underline n}` (proper colorings = injections =
    embeddings, via `Fintype.card_embedding_eq`).
  * `deletion_contraction`: the headline result. Splitting the proper colorings of `G - e` by the
    decidable predicate `c a = c b` separates them into the proper colorings of `G` (endpoints get
    distinct colors, `properColorings_delEdge_filter_ne`) and the proper colorings of the contraction
    `G / e` (endpoints get equal colors, `card_delEdge_filter_eq`).
  * The contraction bijection (`card_delEdge_filter_eq`) is the technical core: restrict a coloring to
    `{v // v ≠ b}` in one direction and re-extend `b ↦ a`'s color in the other; properness transfers
    because `contract`'s adjacency redirects `b`'s neighbors to `a`.

CRITIQUE / ADVERSARIAL REVIEW.
  * None of the main theorems is vacuous: `chromVal_top` is a nonconstant closed form, and
    deletion–contraction is verified numerically (P₃ = K₃ − e gives 12 = 6 + 6 at q = 3).
  * Edge case `a = b` is excluded automatically since the recurrence hypothesis is `G.Adj a b`, which
    forces `a ≠ b`; the contraction's domain `{v // v ≠ b}` is then nondegenerate.
  * The contraction is modeled on a subtype rather than a quotient; this is faithful because proper
    colorings only see *which* vertices are merged, and merging `b` into `a` with redirected
    incidences reproduces exactly the colorings with `c a = c b`.

VERIFICATION.  `#print axioms deletion_contraction` = [propext, Classical.choice, Quot.sound]; the
file compiles with 0 sorries.
-- !-- End Lab Notes -- !--
-/


open Catalog.Combinatorics.ChromaticPolynomial in
theorem solution{G : SimpleGraph V} [DecidableRel G.Adj]
    {α : Type*} [Fintype α] [DecidableEq α] (c : V → α) :
    c ∈ properColorings G α ↔ ∀ x y, G.Adj x y → c x ≠ c y := by
  simp [properColorings]
