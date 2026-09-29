-- Prove2me | Theorems.Thm_Novelty_Catalog_Combinatorics_ChromaticPolynomial_chromVal_pos_iff_colorable
-- name    : Novelty.Catalog.Combinatorics.ChromaticPolynomial.chromVal_pos_iff_colorable
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-18T00:14:52.205734+00:00
-- url     : https://prove2.me/theorems/66975ae5-8f1a-4fc0-a077-da235f80f952
-- title:
--   ChromVal pos iff colorable
-- statement:
--   Formal statement of `Catalog.Combinatorics.ChromaticPolynomial.chromVal_pos_iff_colorable` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Catalog.Combinatorics.ChromaticPolynomial.chromVal_pos_iff_colorable(G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) :
--       0 < chromVal G q ↔ G.Colorable q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ChromaticPolynomialColorable.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ChromaticPolynomialColorable.lean#L56

-- Thm stub generated from Novelty/ChromaticPolynomialColorable.lean
import Mathlib
import Definitions.Def_Novelty_ChromaticPolynomial
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

theorem Novelty.Catalog.Combinatorics.ChromaticPolynomial.chromVal_pos_iff_colorable(G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) :
    0 < chromVal G q ↔ G.Colorable q := by sorry
