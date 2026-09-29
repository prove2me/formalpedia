-- Prove2me | Theorems.Thm_TriangularForest_maxPath_idx_injOn
-- name    : TriangularForest.maxPath_idx_injOn
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:58:59.780944+00:00
-- url     : https://prove2.me/theorems/9677ccde-9b58-4171-8f5d-572211c37735
-- title:
--   Positions along a path determine vertices, so distinct neighbours of the starting point of a
-- statement:
--   Positions along a path determine vertices, so distinct neighbours of the starting point of a
--   maximum length path occupy distinct positions.
--
--   ```lean
--   theorem TriangularForest.maxPath_idx_injOn{a b : V} (p : G.Walk a b) (hp : p.IsPath)
--       (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length ≤ p.length) :
--       Set.InjOn (fun x => p.support.idxOf x) (G.neighborFinset a : Set V) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/TriangularForest/Sparsity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/TriangularForest/Sparsity.lean#L117

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

theorem TriangularForest.maxPath_idx_injOn{a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length ≤ p.length) :
    Set.InjOn (fun x => p.support.idxOf x) (G.neighborFinset a : Set V) := by sorry
