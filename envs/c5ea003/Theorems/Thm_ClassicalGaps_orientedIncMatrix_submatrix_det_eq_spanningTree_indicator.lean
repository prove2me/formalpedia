-- Prove2me | Theorems.Thm_ClassicalGaps_orientedIncMatrix_submatrix_det_eq_spanningTree_indicator
-- name    : ClassicalGaps.orientedIncMatrix_submatrix_det_eq_spanningTree_indicator
-- status  : Proved
-- author  : @Rizwan G Mir
-- created : 2026-09-24T20:28:26.344983+00:00
-- url     : https://prove2.me/theorems/b7494e0f-44ce-424e-8236-691d3f099762
-- title:
--   A reduced incidence submatrix has determinant ±1 on a spanning tree and 0 otherwise
-- statement:
--   Let $G$ be a finite simple graph on vertex set $V$ with oriented incidence matrix $B$ (`ClassicalGaps.orientedIncMatrix`), fix a base vertex $v_0$, let $F$ be a set of $|V|-1$ edges of $G$, and fix any bijection $e$ between $V\setminus\{v_0\}$ and $F$. Form the square matrix $M_{a,b} = B_{a, e(b)}$ indexed by $V \setminus \{v_0\}$ (deleting the row for $v_0$ and reindexing the columns from $F$ through $e$). Then $\det(M)^2$ is $1$ if the edges in $F$ form a spanning tree of $G$ (the subgraph they induce is connected), and $0$ otherwise. Squaring makes the statement independent of the choice of $e$ and of sign conventions.
--
--   This is the key combinatorial fact in Kirchhoff's matrix-tree theorem: combined with the Cauchy-Binet formula (`ClassicalGaps.cauchy_binet_det`) applied to `ClassicalGaps.lapMatrix_eq_orientedIncMatrix_mul_transpose`, it turns the sum of squared minors into exactly the count of spanning trees. The classical proof is by induction on $|F|$: if $F$ contains a cycle the columns are linearly dependent (determinant $0$); if $F$ is a spanning tree, expanding along a leaf vertex's row gives $\pm 1$ times the determinant for the smaller tree with that leaf removed.
--
--   Formalization Note: child lemma of `ClassicalGaps.kirchhoff_matrix_tree`.

import Mathlib
import Definitions.Def_ClassicalGaps_orientedIncMatrix
open Classical Matrix

namespace ClassicalGaps

theorem orientedIncMatrix_submatrix_det_eq_spanningTree_indicator
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v₀ : V) (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) (hcard : F.card + 1 = Fintype.card V)
    (e : {x : V // x ≠ v₀} ≃ {x // x ∈ F}) :
    (Matrix.of (fun a b : {x : V // x ≠ v₀} => orientedIncMatrix G a.1 ((e b : Sym2 V)))).det ^ 2 =
      (if (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Connected then (1:ℝ) else 0) := by sorry

end ClassicalGaps
