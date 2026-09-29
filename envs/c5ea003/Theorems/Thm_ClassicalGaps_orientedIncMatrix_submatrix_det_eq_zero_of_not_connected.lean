-- Prove2me | Theorems.Thm_ClassicalGaps_orientedIncMatrix_submatrix_det_eq_zero_of_not_connected
-- name    : ClassicalGaps.orientedIncMatrix_submatrix_det_eq_zero_of_not_connected
-- status  : Proved
-- author  : @Rizwan G Mir
-- created : 2026-09-26T20:32:38.862628+00:00
-- url     : https://prove2.me/theorems/ce8c48e3-2298-4f5c-b421-a76acdf7d005
-- title:
--   Incidence minor has determinant zero when the edge set is disconnected
-- statement:
--   Let $G$ be a finite simple graph with oriented incidence matrix $B$ (rows indexed by vertices, columns by edges; each edge column has $+1$ and $-1$ at its two endpoints). Fix a vertex $v_0$ and a set $F$ of edges of $G$ with $|F| = |V|-1$, and let $M$ be the square matrix obtained from $B$ by deleting the row of $v_0$ and keeping only the columns in $F$.
--
--   If the graph on $V$ with edge set $F$ is **not connected**, then
--   $$\det M = 0.$$
--
--   This is the "disconnected" half of the key lemma in the standard proof of Kirchhoff's matrix-tree theorem (the determinant of such a minor is $\pm 1$ when $F$ is a spanning tree and $0$ otherwise). The reason: some connected component $C$ of $(V,F)$ misses $v_0$, and the rows of $M$ indexed by $C$ sum to zero, since every edge of $F$ has either both endpoints in $C$ (contributing $+1-1$) or neither.
-- source:
--   Standard proof of Kirchhoff's matrix-tree theorem; see e.g. Bollobás, Modern Graph Theory, Section II.3 (Theorem 12 and its proof). Child lemma of ClassicalGaps.orientedIncMatrix_submatrix_det_eq_spanningTree_indicator.

import Mathlib
import Definitions.Def_ClassicalGaps_orientedIncMatrix
open Classical Matrix

namespace ClassicalGaps

theorem orientedIncMatrix_submatrix_det_eq_zero_of_not_connected
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v₀ : V) (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset)
    (e : {x : V // x ≠ v₀} ≃ {x // x ∈ F})
    (hnc : ¬ (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Connected) :
    (Matrix.of (fun a b : {x : V // x ≠ v₀} => orientedIncMatrix G a.1 ((e b : Sym2 V)))).det = 0 := by sorry

end ClassicalGaps
