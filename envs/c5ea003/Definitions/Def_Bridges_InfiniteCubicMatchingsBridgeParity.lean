-- Prove2me | Definitions.Def_Bridges_InfiniteCubicMatchingsBridgeParity
-- name    : Bridges_InfiniteCubicMatchingsBridgeParity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:25:13.009261+00:00
-- url     : https://prove2.me/theorems/72116044-9484-4d55-9fc3-90b26289b4b0
-- title:
--   Aether Catalog definitions — Bridges_InfiniteCubicMatchingsBridgeParity
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.InfiniteCubicMatchingsBridgeParity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/InfiniteCubicMatchingsBridgeParity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
/-
# Cut parity in cubic graphs, and bridges versus finite sides

`InfiniteCubicMatchings.lean` proves that a graph possessing a **one-edge odd cut** satisfies
none of the three properties (`not_bergeFulkerson_of_oddCut_singleton` and friends), where
`IsOddCut G {e}` asks for a finite vertex set `S` of *odd* cardinality with
`cutEdges G S = {e}`.  In the finite world one never checks that parity by hand: a cubic graph
with a bridge automatically has an odd side, by the handshake lemma.  In the infinite world the
argument has to be redone for a *finite side of a possibly infinite graph*, and doing so was
next-cycle sub-conjecture 3 of `FUTURE_DIRECTIONS.md`.

This file proves it, in the sharpest form available.  The engine is
`cutEdges_finite_and_handshake`: for a cubic graph and **any** finite vertex set `S`, the cut
`cutEdges G S` is finite and

  `3 * S.card = 2 * m + (cutEdges G S).ncard`   for some `m`,

by a half-edge count — the set of pairs `(v, w)` with `v ∈ S` and `v` adjacent to `w` has
exactly `3 * S.card` elements; the pairs with `w ∈ S` form a set stable under a fixed-point-free
involution (swap), hence of even size; and the pairs with `w ∉ S` are in bijection with the cut.
Consequently `S.card` and `(cutEdges G S).ncard` always have the *same parity*
(`odd_card_iff_odd_ncard_cutEdges`), which is the infinite-graph form of the classical
"odd side ⟺ odd cut" for cubic graphs.

Consequences:

* `isOddCut_iff_odd_ncard` : for a cubic graph, `C` is an odd cut in the sense of `IsOddCut`
  iff it is the cut of some finite vertex set and has an odd number of edges;
* `isOddCut_singleton_iff` : in particular the parity hypothesis is automatic for one-edge
  cuts, so the obstruction in `not_bergeFulkerson_of_oddCut_singleton` is exactly
  "a one-edge cut with a finite side";
* `cutEdgesSet_bridgeSide` : the vertex set reachable from `u` after deleting a bridge
  `s(u, w)` has exactly `{s(u, w)}` as its cut;
* `not_bergeFulkerson_of_bridge_with_finite_side` (and the `FanRaspaud` / `MacajovaSkoviera`
  versions) : a cubic graph with a bridge one of whose sides is finite satisfies none of the
  three properties;
* `bridge_sides_infinite_of_bergeFulkerson` : hence, in a cubic graph satisfying
  Berge–Fulkerson, **every bridge separates two infinite sides**.  Together with
  `exists_bridged_cubic_bergeFulkerson` of `…Bridged.lean` this is sharp; the two halves are
  combined in `…BridgeSharp.lean`.
-/

namespace Bridges.InfiniteCubicMatchings

universe u

variable {V : Type u} {G : SimpleGraph V}

/-! ## The half-edge count -/









/-! ## Bridges -/

/-- The set of vertices still reachable from `u` after deleting the edge `s(u, w)`. -/
def bridgeSide (G : SimpleGraph V) (u w : V) : Set V :=
  {x | (G \ SimpleGraph.fromEdgeSet {s(u, w)}).Reachable u x}











end Bridges.InfiniteCubicMatchings


