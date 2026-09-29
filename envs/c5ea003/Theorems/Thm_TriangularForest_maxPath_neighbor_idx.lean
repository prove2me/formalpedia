-- Prove2me | Theorems.Thm_TriangularForest_maxPath_neighbor_idx
-- name    : TriangularForest.maxPath_neighbor_idx
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:58:54.595885+00:00
-- url     : https://prove2.me/theorems/e2a8eb4c-a23c-4fff-8c28-f3258523bbc0
-- title:
--   A neighbour of the starting point of a maximum length path in a triangular forest sits at
-- statement:
--   A neighbour of the starting point of a maximum length path in a triangular forest sits at
--   position `1` or `2` along the path: further along it would close a cycle of length `≥ 4`.
--
--   ```lean
--   theorem TriangularForest.maxPath_neighbor_idx{a b : V} (hG : IsTriangularForest G) (p : G.Walk a b)
--       (hp : p.IsPath) (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length ≤ p.length)
--       {x : V} (hx : x ∈ G.neighborFinset a) :
--       p.support.idxOf x = 1 ∨ p.support.idxOf x = 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/TriangularForest/Sparsity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/TriangularForest/Sparsity.lean#L88

-- Thm stub generated from Logic/TriangularForest/Sparsity.lean
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

theorem TriangularForest.maxPath_neighbor_idx{a b : V} (hG : IsTriangularForest G) (p : G.Walk a b)
    (hp : p.IsPath) (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length ≤ p.length)
    {x : V} (hx : x ∈ G.neighborFinset a) :
    p.support.idxOf x = 1 ∨ p.support.idxOf x = 2 := by sorry
