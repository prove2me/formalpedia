-- Prove2me | Definitions.Def_Bridges_GraphTheory_EulerTheorem
-- name    : Bridges_GraphTheory_EulerTheorem
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:22:17.191381+00:00
-- url     : https://prove2.me/theorems/7f7a1f02-40fe-460b-8ee3-36b3034259dd
-- title:
--   Aether Catalog definitions — Bridges_GraphTheory_EulerTheorem
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GraphTheory.EulerTheorem`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GraphTheory/EulerTheorem.lean by skeleton subtraction
import Mathlib

/-!
# Euler's Bridge Theorem

This file formalizes Euler's theorem on Eulerian circuits in simple graphs,
inspired by the famous Königsberg Bridge Problem (1736).

The central result is that **if a graph admits an Eulerian circuit, then every
vertex has even degree**. This is proved by establishing that in any closed walk,
each vertex is incident to an even number of edges — a fact we call the
*Walk Incidence Parity Lemma*. Combined with a trail covering all edges, this
forces every degree to be even.

We also prove the **Odd-Degree Parity Theorem**: in any finite graph, the number
of vertices with odd degree is always even. This is a direct corollary of the
Handshaking Lemma (which is already in Mathlib).

## Main Results

* `Bridges.walk_incidenceCount_mod2` — The parity of the incidence count of any
  vertex in a walk depends only on whether the vertex is an endpoint.
* `Bridges.circuit_incidenceCount_even` — In a closed walk, every vertex has
  even incidence count.
* `Bridges.eulerian_circuit_implies_even_degree` — If a graph has an Eulerian
  circuit, then every vertex has even degree.
* `Bridges.card_odd_degree_vertices_even` — The number of vertices with odd
  degree in any finite graph is even.

## References

* Euler, L. "Solutio problematis ad geometriam situs pertinentis." 1736.
-/

namespace Bridges

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

section WalkIncidence

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The number of edges in a walk's edge list that are incident to a given vertex. -/
noncomputable def Walk.incidenceCount {u v : V} (w : G.Walk u v) (x : V) : ℕ :=
  w.edges.countP (fun e => x ∈ e)

/-
**Walk Incidence Parity Lemma**: In a walk from `u` to `v`, the incidence
count of a vertex `x` has the same parity as the number of endpoints equal to `x`.

This is the combinatorial heart of Euler's theorem. The proof proceeds by
induction on the walk structure.
-/

/-
In any closed walk, every vertex has even incidence count.
-/

end WalkIncidence

section EulerianCircuit

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- An Eulerian circuit is a circuit (closed trail) that traverses every edge
of the graph exactly once. -/
def IsEulerianCircuit {v : V} (w : G.Walk v v) : Prop :=
  w.IsCircuit ∧ ∀ e ∈ G.edgeFinset, e ∈ w.edges

/-
The edge list of an Eulerian circuit, viewed as a finset, equals the
graph's edge finset.
-/

/-
The number of edges in a graph's edge finset that are incident to a given
vertex equals the degree of that vertex.
-/

/-
In an Eulerian circuit, the incidence count of any vertex equals its degree.
-/


end EulerianCircuit

section OddDegree

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-
**Odd-Degree Parity Theorem**: The number of vertices with odd degree in any
finite graph is always even. This is a direct corollary of the Handshaking Lemma
(`SimpleGraph.sum_degrees_eq_twice_card_edges`).
-/

end OddDegree

end Bridges


