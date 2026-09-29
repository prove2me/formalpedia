-- Prove2me | Theorems.Thm_DegreeSpillCounterexample_spillGraph_hasPEO
-- name    : DegreeSpillCounterexample.spillGraph_hasPEO
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:25:19.471426+00:00
-- url     : https://prove2.me/theorems/a854ebf4-a840-4f11-a515-800935718ab6
-- title:
--   The natural vertex order is a perfect elimination order.
-- statement:
--   The natural vertex order is a perfect elimination order.  Thus the example lies in the
--   chordal/SSA graph class, rather than exploiting an induced long cycle.
--
--   ```lean
--   theorem DegreeSpillCounterexample.spillGraph_hasPEO: HasPerfectEliminationOrder spillGraph := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/RegisterAllocationDegreeSpill.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/RegisterAllocationDegreeSpill.lean#L71

-- Thm stub generated from Novelty/RegisterAllocationDegreeSpill.lean
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

theorem DegreeSpillCounterexample.spillGraph_hasPEO: HasPerfectEliminationOrder spillGraph := by sorry
