-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.Ladder.ladder_neighborSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:26:07.774196+00:00
-- url     : https://prove2.me/submissions/56905c48-265c-4305-9f3c-15dfbdca9492

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











open Bridges.InfiniteCubicMatchings.Ladder in
theorem solution(p : ℤ × Bool) :
    ladder.neighborSet p = {(p.1, !p.2), (p.1 + 1, p.2), (p.1 - 1, p.2)} := by
  obtain ⟨n, b⟩ := p
  ext ⟨m, c⟩
  simp only [SimpleGraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1.symm, by cases b <;> cases c <;> simp_all⟩
    · rcases h2 with h2 | h2
      · exact Or.inr (Or.inl ⟨by simp only at h2; omega, h1.symm⟩)
      · exact Or.inr (Or.inr ⟨by simp only at h2; omega, h1.symm⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, by cases b <;> simp⟩
    · exact Or.inr ⟨rfl, Or.inl rfl⟩
    · exact Or.inr ⟨rfl, Or.inr (by omega)⟩
