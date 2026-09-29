-- Prove2me | Definitions.Def_Bridges_GraphTheory_EulerianImpossibility
-- name    : Bridges_GraphTheory_EulerianImpossibility
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:22:19.538888+00:00
-- url     : https://prove2.me/theorems/1a2954db-4f13-4548-9aee-7e63ec6d5bed
-- title:
--   Aether Catalog definitions — Bridges_GraphTheory_EulerianImpossibility
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GraphTheory.EulerianImpossibility`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GraphTheory/EulerianImpossibility.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Eulerian Impossibility: The Königsberg Bridge Theorem

This file formalizes the mathematical core of Euler's 1736 resolution of the
Königsberg Bridge Problem — the result that launched graph theory.

## Main Results

* `K4_degree` — Every vertex of the complete graph K₄ has degree 3.
* `K4_odd_degree_card` — All 4 vertices of K₄ have odd degree.
* `K4_no_eulerian_walk` — K₄ admits no Eulerian walk (trail visiting every edge exactly once).
* `odd_degree_eulerian_obstruction` — General theorem: a graph with more than 2
  odd-degree vertices admits no Eulerian walk.

## Historical Context

In 1736, Leonhard Euler proved that no walk through the city of Königsberg could
cross each of its seven bridges exactly once. His proof introduced the concept of
what we now call a graph, and established the first theorem of graph theory:
a connected graph has an Eulerian trail if and only if it has at most two vertices
of odd degree.
-/


open SimpleGraph Finset

namespace Bridges

/-- The complete graph on 4 vertices (K₄), our proxy for the Königsberg bridge structure.
    Like the Königsberg graph, every vertex of K₄ has odd degree. -/
abbrev K4 : SimpleGraph (Fin 4) := ⊤

/-
Every vertex of K₄ has degree exactly 3.
-/

/-
The number of odd-degree vertices in K₄ is 4 (all of them).
-/

/-
**Eulerian Obstruction Theorem.** A finite simple graph with more than 2 odd-degree
    vertices admits no Eulerian walk. This is the contrapositive of the necessary
    condition from Euler's theorem.
-/

/-
**K₄ has no Eulerian walk.** No walk on the complete graph K₄ traverses every edge
    exactly once. This is the graph-theoretic essence of the Königsberg Bridge Problem.
-/

end Bridges


