-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.k4Chain_isBridge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:58:32.775075+00:00
-- url     : https://prove2.me/submissions/b4fc88aa-a1b8-4a45-930d-2822992a157a

-- Sol generated from Bridges/InfiniteCubicMatchingsBridged.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchingsBridged
import Definitions.Def_Bridges_InfiniteCubicMatchingsPetersenLift
import Theorems.Thm_Bridges_InfiniteCubicMatchings_k4Chain_separating
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

/-- Walking inside a graph cannot change the side of a set that no edge crosses. -/
theorem mem_iff_of_walk {H : SimpleGraph V} {S : Set V}
    (hsep : ∀ a b, H.Adj a b → (a ∈ S ↔ b ∈ S)) :
    ∀ {a b : V}, H.Walk a b → (a ∈ S ↔ b ∈ S) := by
  intro a b w
  induction w with
  | nil => exact Iff.rfl
  | cons h _ ih => exact (hsep _ _ h).trans ih

/-- If no edge of `H` crosses `S`, then no vertex of `S` reaches a vertex outside `S`. -/
theorem not_reachable_of_separating {H : SimpleGraph V} {S : Set V}
    (hsep : ∀ a b, H.Adj a b → (a ∈ S ↔ b ∈ S)) {a b : V} (ha : a ∈ S) (hb : b ∉ S) :
    ¬ H.Reachable a b := by
  rintro ⟨w⟩
  exact hb ((mem_iff_of_walk hsep w).mp ha)

/-! ## `K₄` and its three perfect matchings -/








/-! ## Unrolling one edge of `K₄` along ℤ -/









/-! ## The chain has infinitely many bridges -/







open Bridges.InfiniteCubicMatchings in
theorem solution(m : ℤ) :
    k4Chain.IsBridge s((m, (3 : Fin 4)), (m + 1, (0 : Fin 4))) := by
  rw [SimpleGraph.isBridge_iff]
  refine ⟨⟨show (3 : Fin 4) ≠ (0 : Fin 4) by decide, by simp [k4Vol]⟩, ?_⟩
  refine not_reachable_of_separating (k4Chain_separating m) ?_ ?_
  · show m ≤ m
    exact le_refl _
  · show ¬ (m + 1 ≤ m)
    omega
