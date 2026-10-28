-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_edge_bound
-- name    : WilliamsonShmoys.edge_maximal_planar_graph_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:16:47.269985+00:00
-- url     : https://prove2.me/theorems/8b15ff15-1296-4ad5-adda-4641353d6263
-- title:
--   Edge bound for an edge-maximal planar graph
-- statement:
--   An edge-maximal simple graph with a planar drawing on at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_graph_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V, M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N <= M) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by sorry
