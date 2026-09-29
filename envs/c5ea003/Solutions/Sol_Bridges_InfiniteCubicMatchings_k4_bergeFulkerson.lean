-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.k4_bergeFulkerson
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:50:41.611244+00:00
-- url     : https://prove2.me/submissions/26648ce2-b806-40c0-a961-bd01c99f221f

-- Sol generated from Bridges/InfiniteCubicMatchingsBridged.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsBridged
import Definitions.Def_Bridges_InfiniteCubicMatchingsPetersenLift
import Theorems.Thm_Bridges_InfiniteCubicMatchings_ProperThreeEdgeColoring_bergeFulkerson
import Theorems.Thm_Bridges_InfiniteCubicMatchings_k4_properThreeEdgeColoring
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
theorem solution: BergeFulkerson k4 := k4_properThreeEdgeColoring.bergeFulkerson
