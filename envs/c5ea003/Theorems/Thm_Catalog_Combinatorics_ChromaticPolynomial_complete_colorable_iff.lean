-- Prove2me | Theorems.Thm_Catalog_Combinatorics_ChromaticPolynomial_complete_colorable_iff
-- name    : Catalog.Combinatorics.ChromaticPolynomial.complete_colorable_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:05:16.928621+00:00
-- url     : https://prove2.me/theorems/eab50e73-7bb3-4477-a0c5-e6f2b17c3295
-- title:
--   Complete colorable iff
-- statement:
--   Formal statement of `Catalog.Combinatorics.ChromaticPolynomial.complete_colorable_iff` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Catalog.Combinatorics.ChromaticPolynomial.complete_colorable_iff(q : ℕ) :
--       (⊤ : SimpleGraph V).Colorable q ↔ Fintype.card V ≤ q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/ChromaticPolynomialColorable.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/ChromaticPolynomialColorable.lean#L86

-- Thm stub generated from Geometry/ChromaticPolynomialColorable.lean
import Mathlib
import Definitions.Def_Geometry_ChromaticPolynomial
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Chromatic Counting Function as a Colorability Oracle

This file connects the chromatic counting function `chromVal` from `ChromaticPolynomial.lean` to
Mathlib's `SimpleGraph.Colorable` and `SimpleGraph.chromaticNumber`, and records the structural
corollaries of the deletion–contraction recurrence.

Main results:

  * `chromVal_pos_iff_colorable` :  `0 < P(G, q) ↔ G.Colorable q`
        (the chromatic polynomial detects colorability: it is positive exactly when a proper
        `q`-coloring exists).
  * `chromaticNumber_le_iff_chromVal_pos` :  `χ(G) ≤ q ↔ 0 < P(G, q)`
        (the chromatic number is the least `q` with `P(G,q) > 0`).
  * `chromVal_le_delEdge` :  `P(G, q) ≤ P(G − e, q)`
        (deleting an edge can only increase the number of proper colorings) — an immediate
        consequence of deletion–contraction, since the contraction term is nonnegative.
  * `complete_colorable_iff` :  `K_n` is `q`-colorable `↔ n ≤ q`, obtained by feeding the
        falling-factorial evaluation `chromVal_top` into `chromVal_pos_iff_colorable`.

-- !-- Lab Notes -- !--
HYPOTHESIS.  The chromatic *polynomial* and the chromatic *number* should be two views of the same
data: `P(G,q) > 0` should hold exactly when `G` admits a proper `q`-coloring, so the chromatic number
is the smallest `q` making `P(G,q)` positive.

EXPERIMENTAL PLAN.  (1) Convert positivity of a finset cardinality into nonemptiness, then into the
existence of a proper coloring function, then into `G.Colorable q` via `Coloring.mk`.  (2) Chain with
Mathlib's `chromaticNumber_le_iff_colorable`.  (3) Read off edge-deletion monotonicity from
`deletion_contraction_chromVal` (the contraction count is `≥ 0`).  (4) Specialize `chromVal_top` to
get a closed criterion for colorability of the complete graph.

INSIGHT.  Once colorability is expressed as `0 < chromVal`, deletion–contraction yields a *monotone*
statement for free: removing an edge adds the (nonnegative) contraction count, so the coloring count
never decreases.  This is the counting shadow of `chromaticNumber_mono`.

ANALYSIS.  `complete_colorable_iff` is a genuine cross-check: it is proved here purely from the
chromatic-polynomial side (`descFactorial q n > 0 ↔ n ≤ q`) yet recovers the classical fact that
`χ(K_n) = n`, independent of Mathlib's `chromaticNumber_top`.
-- !-- End Lab Notes -- !--
-/

open Catalog.Combinatorics.ChromaticPolynomial

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
**Colorability oracle.** The chromatic polynomial is positive at `q` exactly when `G` admits a
proper coloring with `q` colors.
-/

/-
**The chromatic number is the least positivity point.** `χ(G) ≤ q` iff `P(G, q) > 0`.
-/

/-
**Edge-deletion monotonicity.** Deleting an edge cannot decrease the number of proper
colorings; this is immediate from deletion–contraction.
-/

/-
**Colorability of the complete graph.** `K_n` is `q`-colorable iff `n ≤ q`, proved from the
falling-factorial evaluation of its chromatic polynomial.
-/

theorem Catalog.Combinatorics.ChromaticPolynomial.complete_colorable_iff(q : ℕ) :
    (⊤ : SimpleGraph V).Colorable q ↔ Fintype.card V ≤ q := by sorry
