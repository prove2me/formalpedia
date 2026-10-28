-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_edge_count_for_maximal_drawing_bound
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_edge_count_for_maximal_drawing_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:03:03.695481+00:00
-- url     : https://prove2.me/theorems/e0af0c25-eda4-4a07-86fb-83c9b4328991
-- title:
--   Triangulation extension for a maximal drawable graph bound
-- statement:
--   Every drawable simple graph on at least three vertices is a subgraph of a drawable graph on the same vertices with exactly 3|V|−6 edges. This is the new core lemma: a plane embedding can be extended by adding noncrossing edges until every face is triangular, after which Euler’s formula gives the edge count. The parent uses maximality to identify this extension with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_supergraph_edge_count_for_maximal_drawing_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V = N.edgeSet.ncard + 6 := by sorry
