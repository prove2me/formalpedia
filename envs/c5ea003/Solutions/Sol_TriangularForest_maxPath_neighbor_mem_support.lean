-- Prove2me | solution 1 for TriangularForest.maxPath_neighbor_mem_support
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:45:00.93018+00:00
-- url     : https://prove2.me/submissions/0df5c4ee-8770-435a-82c9-871a5a0eabc5

-- Sol generated from Logic/TriangularForest/Sparsity.lean
import Mathlib
import Definitions.Def_Logic_TriangularForest_Defs

/-!
# Sparsity of triangular forests

The main result of this file is that triangular forests are *sparse*: a triangular forest on
`n ≥ 2` vertices has at most `2n - 3` edges (`TriangularForest.card_edgeFinset_add_three_le`).

The proof runs through a longest-path argument, which is the combinatorial heart of the file:

* `TriangularForest.exists_maxPath` — a finite nonempty graph has a path of maximum length;
* `TriangularForest.degree_le_two_of_maxPath_endpoint` — in a triangular forest the endpoint of
  a maximum length path has degree at most two.  Indeed all its neighbours lie on the path (else
  the path could be extended), and a neighbour sitting at distance `ℓ ≥ 2` along the path closes
  a cycle of length `ℓ + 1`, which must be `3`;
* `TriangularForest.exists_degree_le_two` — hence every finite nonempty triangular forest has a
  vertex of degree at most two (triangular forests are `2`-degenerate);
* the edge bound then follows by induction on the number of vertices, deleting a vertex of
  degree at most two.
-/

open TriangularForest

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}




variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]










open TriangularForest in
theorem solution{a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length ≤ p.length)
    {x : V} (hx : x ∈ G.neighborFinset a) : x ∈ p.support := by
  by_contra hnot
  have hadj : G.Adj x a := ((G.mem_neighborFinset a x).1 hx).symm
  have hpath : (Walk.cons hadj p).IsPath := hp.cons hnot
  have := hmax x b (Walk.cons hadj p) hpath
  simp [Walk.length_cons] at this
