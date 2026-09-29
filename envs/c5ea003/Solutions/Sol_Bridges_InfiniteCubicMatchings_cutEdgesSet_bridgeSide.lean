-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.cutEdgesSet_bridgeSide
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:33:52.358603+00:00
-- url     : https://prove2.me/submissions/5e29724a-62d6-4f75-8eba-87df2dad9f50

-- Sol generated from Bridges/InfiniteCubicMatchingsBridgeParity.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsBridgeParity
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

open Bridges.InfiniteCubicMatchings

universe u

variable {V : Type u} {G : SimpleGraph V}

/-! ## The half-edge count -/









/-! ## Bridges -/













open Bridges.InfiniteCubicMatchings in
theorem solution{u w : V} (h : G.IsBridge s(u, w)) :
    cutEdgesSet G (bridgeSide G u w) = {s(u, w)} := by
  rw [SimpleGraph.isBridge_iff] at h
  obtain ⟨hadj, hnr⟩ := h
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨⟨hadj, u, w, rfl, SimpleGraph.Reachable.refl u, hnr⟩, ?_⟩
  rintro f ⟨hfE, a, b, rfl, haS, hbS⟩
  by_contra hne
  -- if `s(a, b)` is not the deleted edge it survives the deletion, so `b` is on `u`'s side
  have hadj' : (G \ SimpleGraph.fromEdgeSet {s(u, w)}).Adj a b := by
    refine ⟨hfE, ?_⟩
    rintro ⟨hmem, -⟩
    exact hne (Set.mem_singleton_iff.mp hmem)
  exact hbS (haS.trans hadj'.reachable)
