-- Prove2me | Definitions.Def_Logic_TriangularForest_Defs
-- name    : Logic_TriangularForest_Defs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:10:24.414484+00:00
-- url     : https://prove2.me/theorems/85b85f6a-a2f6-47cf-bfde-4b8bd604f9d6
-- title:
--   Aether Catalog definitions — Logic_TriangularForest_Defs
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.TriangularForest.Defs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/TriangularForest/Defs.lean by skeleton subtraction
import Mathlib

/-!
# Triangular forests

A *triangular forest* is a graph in which every 2-connected block is a single edge or a
triangle.  Equivalently (and this is the definition we use, since it is the most convenient
one to reason with) a graph is a triangular forest exactly when **every cycle has length 3**.

The two descriptions agree: a 2-connected graph on at least four vertices always contains a
cycle of length at least four, and two triangles sharing an edge span a 4-cycle, so "every
cycle is a triangle" forces every block to be an edge or a triangle, and conversely.

This file sets up the basic theory:

* `TriangularForest.IsTriangularForest` — the definition;
* closure under subgraphs (`IsTriangularForest.mono`) and induced subgraphs
  (`IsTriangularForest.induce`);
* forests are triangular forests;
* every vertex on a cycle has degree at least two, hence a cycle is no longer than the number
  of vertices of degree at least two (`IsCycle.length_le_card_two_le_degree`);
* consequently any graph with at most three vertices of degree ≥ 2 is a triangular forest
  (`isTriangularForest_of_card_two_le_degree_le_three`), which is the workhorse for verifying
  concrete examples.
-/

namespace TriangularForest

open SimpleGraph Finset

variable {V : Type*} {G H : SimpleGraph V}

/-- A graph is a **triangular forest** when every one of its cycles is a triangle. -/
def IsTriangularForest (G : SimpleGraph V) : Prop :=
  ∀ ⦃v : V⦄ (c : G.Walk v v), c.IsCycle → c.length = 3





section Degrees

variable [Fintype V] [DecidableRel G.Adj]


variable [DecidableEq V]



end Degrees

end TriangularForest


