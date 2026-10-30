-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulation_maximal_planar_edge_count
-- name    : WilliamsonShmoys.triangulation_maximal_planar_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:01:42.309164+00:00
-- url     : https://prove2.me/theorems/ef9edf2c-0072-4fb0-90f6-e8c17c2e2067
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices whose edge count is maximal among drawable supergraphs on the same vertex type has exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.triangulation_maximal_planar_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ W : SimpleGraph V, U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W →
      W.edgeSet.ncard ≤ U.edgeSet.ncard) :
    U.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
