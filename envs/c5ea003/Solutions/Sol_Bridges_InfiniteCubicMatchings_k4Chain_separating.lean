-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.k4Chain_separating
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:54:29.623741+00:00
-- url     : https://prove2.me/submissions/c961980f-776b-4577-ad10-f5bef2d99319

-- Sol generated from Bridges/InfiniteCubicMatchingsBridged.lean
import Mathlib
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
theorem solution(m : ℤ) (a b : ℤ × Fin 4)
    (h : (k4Chain \ SimpleGraph.fromEdgeSet {s((m, 3), (m + 1, 0))}).Adj a b) :
    (a ∈ leftLevels m ↔ b ∈ leftLevels m) := by
  obtain ⟨⟨hadj, hlev⟩, hne⟩ := h
  simp only [leftLevels, Set.mem_setOf_eq]
  by_cases h30 : a.2 = 3 ∧ b.2 = 0
  · have hb : b.1 = a.1 + 1 := by
      rw [hlev, k4Vol, if_pos h30]
    by_cases ha0 : a.1 = m
    · exfalso
      refine hne ?_
      have ha' : a = (m, (3 : Fin 4)) := Prod.ext ha0 h30.1
      have hb' : b = (m + 1, (0 : Fin 4)) := Prod.ext (by rw [hb, ha0]) h30.2
      simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff]
      exact ⟨by rw [ha', hb'], by rw [ha', hb']; simp⟩
    · constructor
      · intro _; omega
      · intro _; omega
  · by_cases h03 : a.2 = 0 ∧ b.2 = 3
    · have hb : b.1 = a.1 - 1 := by
        rw [hlev, k4Vol, if_neg h30, if_pos h03]
        ring
      constructor
      · intro _; omega
      · intro hle
        by_contra hgt
        push_neg at hgt
        have ha1 : a.1 = m + 1 := by omega
        exfalso
        refine hne ?_
        have ha' : a = (m + 1, (0 : Fin 4)) := Prod.ext ha1 h03.1
        have hb' : b = (m, (3 : Fin 4)) := Prod.ext (by rw [hb, ha1]; ring) h03.2
        simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff]
        refine ⟨?_, by rw [ha', hb']; simp⟩
        rw [ha', hb', Sym2.eq_swap]
    · have hb : b.1 = a.1 := by
        rw [hlev, k4Vol, if_neg h30, if_neg h03]
        ring
      rw [hb]
