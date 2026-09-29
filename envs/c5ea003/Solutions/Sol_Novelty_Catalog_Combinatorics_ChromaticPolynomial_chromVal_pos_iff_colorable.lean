-- Prove2me | solution 1 for Novelty.Catalog.Combinatorics.ChromaticPolynomial.chromVal_pos_iff_colorable
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T13:45:06.425632+00:00
-- url     : https://prove2.me/submissions/042c5aa5-c2ab-4ed8-af20-debd34456ee9

-- Sol generated from Novelty/ChromaticPolynomialColorable.lean
import Mathlib
import Definitions.Def_Novelty_ChromaticPolynomial
import Theorems.Thm_Novelty_Catalog_Combinatorics_ChromaticPolynomial_mem_properColorings
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


open Catalog.Combinatorics.ChromaticPolynomial in
theorem solution(G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) :
    0 < chromVal G q ↔ G.Colorable q := by
  constructor;
  · intro h_pos
    obtain ⟨c, hc⟩ : ∃ c : V → Fin q, ∀ x y, G.Adj x y → c x ≠ c y := by
      exact Exists.elim ( Finset.card_pos.mp h_pos ) fun c hc => ⟨ _, Novelty.Catalog.Combinatorics.ChromaticPolynomial.mem_properColorings _ |>.1 hc ⟩;
    exact ⟨ c, by aesop ⟩;
  · rintro ⟨ c ⟩;
    refine' Finset.card_pos.mpr ⟨ c.toFun, _ ⟩;
    exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, fun x y hxy => c.valid hxy ⟩
