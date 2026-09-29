-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.k4_isCubic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:01:39.843706+00:00
-- url     : https://prove2.me/submissions/d1c1947b-c710-4f52-9357-b1fe45ee1278

-- Sol generated from Bridges/InfiniteCubicMatchingsBridged.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsBridged
import Definitions.Def_Bridges_InfiniteCubicMatchingsPetersenLift
/-
# Bridges are *not* an obstruction in the infinite setting

For finite cubic graphs, a bridge kills all three conjectures: the bridge is a one-element odd
cut, and `not_bergeFulkerson_of_oddCut_singleton` shows the same in the infinite setting
*provided one side of the cut is finite*.  This file shows that the finiteness proviso is
essential, by exhibiting

  `k4Chain` : an infinite cubic graph, every level of which is a copy of `K₄` with one edge
  "unrolled" along ℤ,

which

* is cubic (`k4Chain_isCubic`),
* satisfies Berge–Fulkerson, Fan–Raspaud and Máčajová–Škoviera
  (`k4Chain_bergeFulkerson`, …), and yet
* **has a bridge** (`k4Chain_isBridge`): in fact every edge joining level `m` to level `m+1`
  is one, so it has infinitely many bridges (`k4Chain_bridges_infinite`).

Hence, unlike in the finite case, bridgelessness is not a necessary condition for any of the
three properties once the graph is infinite: the two sides of the offending cut are infinite,
so the parity argument behind the finite obstruction has nothing to bite on.
-/

open Bridges.InfiniteCubicMatchings

universe u

/-! ## A separation criterion for non-reachability -/

variable {V : Type u}



/-! ## `K₄` and its three perfect matchings -/








/-! ## Unrolling one edge of `K₄` along ℤ -/









/-! ## The chain has infinitely many bridges -/







open Bridges.InfiniteCubicMatchings in
theorem solution: IsCubic k4 := by
  intro v
  rw [show k4.neighborSet v = {u | u ∈ (Finset.univ.filter (fun u => u ≠ v) : Finset (Fin 4))}
      by ext u; simp [k4, SimpleGraph.mem_neighborSet, ne_comm],
    Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
  revert v
  decide
