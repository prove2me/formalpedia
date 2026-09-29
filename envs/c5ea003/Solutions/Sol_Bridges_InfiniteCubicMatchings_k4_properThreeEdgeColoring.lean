-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.k4_properThreeEdgeColoring
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:48:36.951738+00:00
-- url     : https://prove2.me/submissions/b5300c8f-b71c-40ab-ac49-07dc04b13959

-- Sol generated from Bridges/InfiniteCubicMatchingsBridged.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsBridged
import Definitions.Def_Bridges_InfiniteCubicMatchingsPetersenLift
import Theorems.Thm_Bridges_InfiniteCubicMatchings_PerfectMatching_mem_edges
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
theorem solution: ProperThreeEdgeColoring k4 := by
  refine ⟨k4Matching, ?_, ?_⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro e hei hej
    induction e with
    | _ u w =>
      rw [PerfectMatching.mem_edges] at hei hej
      have key : ∀ (i j : Fin 3) (u w : Fin 4), i ≠ j → k4PM i u = w → k4PM j u = w → False := by
        decide
      exact key i j u w hij hei hej
  · intro e
    induction e with
    | _ u w =>
      intro hE
      have key : ∀ u w : Fin 4, u ≠ w → ∃ i : Fin 3, k4PM i u = w := by decide
      obtain ⟨i, hi⟩ := key u w hE
      exact ⟨i, by rw [PerfectMatching.mem_edges]; exact hi⟩
