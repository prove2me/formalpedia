-- Prove2me | solution 1 for DegreeSpillCounterexample.spillGraph_hasPEO
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:50:28.964445+00:00
-- url     : https://prove2.me/submissions/0aed89ed-8932-4c11-a29c-cab1bcbb4e62

-- Sol generated from Novelty/RegisterAllocationDegreeSpill.lean
import Mathlib
import Definitions.Def_Novelty_RegisterAllocationDegreeSpill
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

/-!
# Degree-based spilling is not optimal, even for chordal interference graphs

The exact positive theorem for SSA register allocation is that chordal interference graphs
are perfect, so the register requirement is the clique number, not in general `Δ + 1`.
This file isolates a complementary obstruction to a commonly used heuristic: deleting a
maximum-degree vertex need not be the best one-vertex spill.

The counterexample is itself chordal.  It is the disjoint union of a triangle on vertices
`0,1,2` and a four-leaf star with centre `3`.  The centre has the unique maximum degree four,
but spilling it leaves the uncolourable triangle.  Spilling vertex `0`, whose degree is only
two, leaves an edge and a star, and two registers suffice.

Unlike a bare numerical check, the main result below packages separately proved structural,
degree, positive-colouring, and impossibility lemmas.
-/

open Finset SimpleGraph

open DegreeSpillCounterexample






@[simp] theorem spillGraph_adj (i j : Fin 8) :
    spillGraph.Adj i j ↔
      (i.val < 3 ∧ j.val < 3 ∧ i ≠ j) ∨
      (i.val = 3 ∧ 4 ≤ j.val) ∨
      (j.val = 3 ∧ 4 ≤ i.val) := Iff.rfl











open DegreeSpillCounterexample in
theorem solution: HasPerfectEliminationOrder spillGraph := by
  intro v x hx y hy hxy
  simp [earlierNeighbours] at hx hy
  rcases hx.2 with hxadj | hxadj | hxadj
  · rcases hy.2 with hyadj | hyadj | hyadj
    · exact Or.inl ⟨hxadj.2.1, hyadj.2.1, hxy⟩
    · omega
    · omega
  · omega
  · rcases hy.2 with hyadj | hyadj | hyadj
    · omega
    · omega
    · exact (hxy (Fin.ext (by omega))).elim
