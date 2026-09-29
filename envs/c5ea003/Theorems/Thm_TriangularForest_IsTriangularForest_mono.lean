-- Prove2me | Theorems.Thm_TriangularForest_IsTriangularForest_mono
-- name    : TriangularForest.IsTriangularForest.mono
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:57:29.994467+00:00
-- url     : https://prove2.me/theorems/739deed8-16a9-4e6b-b162-52c2bf93e105
-- title:
--   Triangular forests are closed under taking subgraphs.
-- statement:
--   Triangular forests are closed under taking subgraphs.
--
--   ```lean
--   theorem TriangularForest.IsTriangularForest.mono(hle : H ≤ G) (hG : IsTriangularForest G) :
--       IsTriangularForest H := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/TriangularForest/Defs.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/TriangularForest/Defs.lean#L44

-- Thm stub generated from Logic/TriangularForest/Defs.lean
import Mathlib
import Definitions.Def_Logic_TriangularForest_Defs

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

open TriangularForest

open SimpleGraph Finset

variable {V : Type*} {G H : SimpleGraph V}

theorem TriangularForest.IsTriangularForest.mono(hle : H ≤ G) (hG : IsTriangularForest G) :
    IsTriangularForest H := by sorry
