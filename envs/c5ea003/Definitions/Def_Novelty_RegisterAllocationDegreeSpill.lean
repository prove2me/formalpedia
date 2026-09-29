-- Prove2me | Definitions.Def_Novelty_RegisterAllocationDegreeSpill
-- name    : Novelty_RegisterAllocationDegreeSpill
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:38:37.657863+00:00
-- url     : https://prove2.me/theorems/608a41b4-6d67-4882-8072-1445b828e4ee
-- title:
--   Aether Catalog definitions — Novelty_RegisterAllocationDegreeSpill
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.RegisterAllocationDegreeSpill`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/RegisterAllocationDegreeSpill.lean by skeleton subtraction
import Mathlib
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

namespace DegreeSpillCounterexample

/-- The eight-vertex chordal counterexample: `K₃ ⊔ K₁,₄`. -/
def spillGraph : SimpleGraph (Fin 8) where
  Adj i j :=
    (i.val < 3 ∧ j.val < 3 ∧ i ≠ j) ∨
    (i.val = 3 ∧ 4 ≤ j.val) ∨
    (j.val = 3 ∧ 4 ≤ i.val)
  symm := by
    intro i j h
    rcases h with h | h | h
    · exact Or.inl ⟨h.2.1, h.1, h.2.2.symm⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  loopless := ⟨by
    intro i h
    rcases h with h | h | h
    · exact h.2.2 rfl
    · omega
    · omega⟩

instance : DecidableRel spillGraph.Adj := by
  intro i j
  unfold spillGraph
  infer_instance

/-- Colourability after vertices in `spilled` have been removed.  Colours assigned to removed
vertices are ignored. -/
def ColorableExcept (G : SimpleGraph (Fin 8)) (spilled : Finset (Fin 8)) (k : ℕ) : Prop :=
  ∃ c : Fin 8 → Fin k, ∀ u v, u ∉ spilled → v ∉ spilled → G.Adj u v → c u ≠ c v

/-- Earlier neighbours for the natural elimination order on `Fin 8`. -/
def earlierNeighbours (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj] (v : Fin 8) :
    Finset (Fin 8) := univ.filter (fun w => w < v ∧ G.Adj v w)

/-- The concrete form of a perfect elimination ordering used here. -/
def HasPerfectEliminationOrder (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj] : Prop :=
  ∀ v, G.IsClique (earlierNeighbours G v : Set (Fin 8))











end DegreeSpillCounterexample


