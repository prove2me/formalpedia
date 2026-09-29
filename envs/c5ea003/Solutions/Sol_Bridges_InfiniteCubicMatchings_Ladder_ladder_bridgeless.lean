-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.Ladder.ladder_bridgeless
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:26:07.245819+00:00
-- url     : https://prove2.me/submissions/5b98c01e-c86a-4beb-a714-0e69bfac4ac8

-- Sol generated from Bridges/InfiniteCubicMatchingsLadder.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsLadder
/-
# A concrete infinite cubic bridgeless graph satisfying all three conjectures

The doubly infinite ladder `L` on the vertex set `ℤ × Bool` (rungs `(n,b) — (n,¬b)` and rails
`(n,b) — (n+1,b)`) is an infinite, cubic, bridgeless graph.  We verify all of this formally
and exhibit an explicit proper 3-edge-colouring, which by
`ProperThreeEdgeColoring.bergeFulkerson` yields the Berge–Fulkerson property, hence also the
Fan–Raspaud and Máčajová–Škoviera properties.

This shows that the framework of `Bridges.InfiniteCubicMatchings` is not vacuous: it is
satisfied by a genuinely infinite cubic bridgeless graph.
-/

open Bridges.InfiniteCubicMatchings

open Ladder




/-! ## Three perfect matchings forming a proper 3-edge-colouring -/











/-! ## The ladder is an infinite, cubic, bridgeless graph -/



lemma not_isBridge_of_walk {p q : ℤ × Bool} (w : ladder.Walk p q) (hw : s(p, q) ∉ w.edges) :
    ¬ ladder.IsBridge s(p, q) := by
  rw [SimpleGraph.isBridge_iff]
  rintro ⟨-, hnr⟩
  exact hnr (SimpleGraph.reachable_delete_edges_iff_exists_walk.mpr ⟨w, hw⟩)

/-- Every rung lies on a 4-cycle, hence is not a bridge. -/
lemma not_isBridge_rung (n : ℤ) (b : Bool) : ¬ ladder.IsBridge s((n, b), (n, !b)) := by
  refine not_isBridge_of_walk (SimpleGraph.Walk.cons (adj_rail n b)
    (SimpleGraph.Walk.cons (adj_rung (n + 1) b)
      (SimpleGraph.Walk.cons (by simpa using (adj_rail n (!b)).symm)
        SimpleGraph.Walk.nil))) ?_
  simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
    List.not_mem_nil, or_false, Sym2.eq_iff, Prod.mk.injEq]
  push_neg
  refine ⟨?_, ?_, ?_⟩ <;> constructor <;> intro h <;> simp_all

/-- Every rail lies on a 4-cycle, hence is not a bridge. -/
lemma not_isBridge_rail (n : ℤ) (b : Bool) : ¬ ladder.IsBridge s((n, b), (n + 1, b)) := by
  refine not_isBridge_of_walk (SimpleGraph.Walk.cons (adj_rung n b)
    (SimpleGraph.Walk.cons (adj_rail n (!b))
      (SimpleGraph.Walk.cons (by simpa using adj_rung (n + 1) (!b))
        SimpleGraph.Walk.nil))) ?_
  simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
    List.not_mem_nil, or_false, Sym2.eq_iff, Prod.mk.injEq]
  push_neg
  refine ⟨?_, ?_, ?_⟩ <;> constructor <;> intro h <;> simp_all






open Bridges.InfiniteCubicMatchings.Ladder in
theorem solution: Bridgeless ladder := by
  intro e
  induction e with
  | _ p q =>
    intro he
    obtain ⟨n, b⟩ := p
    obtain ⟨m, c⟩ := q
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only at h1 h2
      subst h1
      have : c = !b := by cases b <;> cases c <;> simp_all
      subst this
      exact not_isBridge_rung n b
    · simp only at h1 h2
      subst h1
      rcases h2 with h2 | h2
      · subst h2
        exact not_isBridge_rail n b
      · have hn : n = m + 1 := h2
        subst hn
        rw [Sym2.eq_swap]
        exact not_isBridge_rail m b
