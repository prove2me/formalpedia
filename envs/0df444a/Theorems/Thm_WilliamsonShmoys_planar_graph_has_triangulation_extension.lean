-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulation_extension
-- name    : WilliamsonShmoys.planar_graph_has_triangulation_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:16:26.737003+00:00
-- url     : https://prove2.me/theorems/2e8a4612-bdce-41b9-ac5a-421bb6c5d32d
-- title:
--   Every finite planar graph extends to a triangulation
-- statement:
--   Any graph with a crossing-free drawing on a finite vertex set of size at least three is a subgraph of a graph on the same vertices with a crossing-free drawing and exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
