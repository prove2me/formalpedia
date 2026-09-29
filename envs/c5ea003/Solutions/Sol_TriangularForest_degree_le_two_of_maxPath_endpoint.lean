-- Prove2me | solution 1 for TriangularForest.degree_le_two_of_maxPath_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:48:57.048462+00:00
-- url     : https://prove2.me/submissions/cce7d329-2d8a-4e1c-b6e0-17af27d5430d

-- Sol generated from Logic/TriangularForest/Sparsity.lean
import Mathlib
import Definitions.Def_Logic_TriangularForest_Defs
import Theorems.Thm_TriangularForest_maxPath_idx_injOn
import Theorems.Thm_TriangularForest_maxPath_neighbor_idx

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
theorem solution    (hG : IsTriangularForest G) {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length ≤ p.length) :
    G.degree a ≤ 2 := by
  classical
  have hmaps : Set.MapsTo (fun x => p.support.idxOf x) (G.neighborFinset a : Set V)
      ((({1, 2} : Finset ℕ) : Set ℕ)) := by
    intro x hx
    have := maxPath_neighbor_idx hG p hp hmax (x := x) (by simpa using hx)
    simpa using this
  have := Finset.card_le_card_of_injOn _ hmaps (maxPath_idx_injOn p hp hmax)
  simpa [card_neighborFinset_eq_degree] using this
