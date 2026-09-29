-- Prove2me | Theorems.Thm_Catalog_Combinatorics_ChromaticPolynomial_chromVal_top
-- name    : Catalog.Combinatorics.ChromaticPolynomial.chromVal_top
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:05:15.095547+00:00
-- url     : https://prove2.me/theorems/1b966b2e-9103-45a9-9d6c-a2ba3b0c0e1d
-- title:
--   ChromVal top
-- statement:
--   Formal statement of `Catalog.Combinatorics.ChromaticPolynomial.chromVal_top` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Catalog.Combinatorics.ChromaticPolynomial.chromVal_top(q : ℕ) :
--       chromVal (⊤ : SimpleGraph V) q = (q).descFactorial (Fintype.card V) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/ChromaticPolynomial.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/ChromaticPolynomial.lean#L126

-- Thm stub generated from Geometry/ChromaticPolynomial.lean
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

theorem Catalog.Combinatorics.ChromaticPolynomial.chromVal_top(q : ℕ) :
    chromVal (⊤ : SimpleGraph V) q = (q).descFactorial (Fintype.card V) := by sorry
