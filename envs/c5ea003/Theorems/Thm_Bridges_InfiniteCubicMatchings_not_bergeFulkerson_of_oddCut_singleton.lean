-- Prove2me | Theorems.Thm_Bridges_InfiniteCubicMatchings_not_bergeFulkerson_of_oddCut_singleton
-- name    : Bridges.InfiniteCubicMatchings.not_bergeFulkerson_of_oddCut_singleton
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:29:08.794064+00:00
-- url     : https://prove2.me/theorems/970386a2-396c-4d66-92e4-c0177e14b960
-- title:
--   Not bergeFulkerson of oddCut singleton
-- statement:
--   Formal statement of `Bridges.InfiniteCubicMatchings.not_bergeFulkerson_of_oddCut_singleton` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Bridges.InfiniteCubicMatchings.not_bergeFulkerson_of_oddCut_singleton{e : Sym2 V} (h : IsOddCut G {e}) :
--       ¬ BergeFulkerson G := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InfiniteCubicMatchings.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InfiniteCubicMatchings.lean#L324

-- Thm stub generated from Bridges/InfiniteCubicMatchings.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
/-
# Perfect matching conjectures in (possibly infinite) cubic bridgeless graphs

This file develops a formal framework, valid for **arbitrary** (finite or infinite) vertex
types, for the three classical perfect-matching conjectures on cubic bridgeless graphs:

* the **Berge–Fulkerson conjecture** (`BergeFulkerson`): six perfect matchings covering
  every edge exactly twice;
* the **Fan–Raspaud conjecture** (`FanRaspaud`): three perfect matchings with empty
  intersection;
* the **Máčajová–Škoviera conjecture** (`MacajovaSkoviera`): two perfect matchings whose
  intersection contains no odd edge cut.

The main results proved here are

* `PerfectMatching.exists_mem_cutEdges` and `PerfectMatching.card_inter_cutEdges_odd`:
  the *parity lemma* in the infinite setting — a perfect matching meets every edge cut with
  a **finite odd side** in an odd (in particular nonzero) number of edges;
* `BergeFulkerson.fanRaspaud` : BF ⟹ FR;
* `FanRaspaud.macajovaSkoviera` : FR ⟹ MŠ (this is where the parity lemma is used);
* `BergeFulkerson.macajovaSkoviera` : BF ⟹ MŠ;
* `not_bergeFulkerson_of_oddCut_singleton` and friends: all three conjectures **fail** for a
  graph possessing a one-edge cut with a finite odd side (the infinite analogue of "a cubic
  graph with a bridge has no such family"); hence bridgelessness is a necessary hypothesis;
* `ProperThreeEdgeColoring.bergeFulkerson` : a 3-edge-colourable graph satisfies BF (by
  doubling the colour classes) — this works verbatim for infinite graphs;
* transport of all three properties along graph isomorphisms.

Everything is stated for an arbitrary vertex type `V`; no finiteness of `V` is assumed
anywhere.
-/

open Bridges.InfiniteCubicMatchings

universe u v

variable {V : Type u} {G : SimpleGraph V}

/-! ## Perfect matchings as fixed-point-free involutions -/


open PerfectMatching









/-! ## Edge cuts with a finite side -/






/-! ## A combinatorial lemma: fixed-point-free involutions have even orbit sets -/


/-! ## The parity lemma -/

open PerfectMatching

variable (M : PerfectMatching G)






/-! ## The three conjectures -/







/-! ## The implications BF ⟹ FR ⟹ MŠ -/




/-! ## Bridgelessness is necessary: one-edge odd cuts destroy all three properties -/

theorem Bridges.InfiniteCubicMatchings.not_bergeFulkerson_of_oddCut_singleton{e : Sym2 V} (h : IsOddCut G {e}) :
    ¬ BergeFulkerson G := by sorry
