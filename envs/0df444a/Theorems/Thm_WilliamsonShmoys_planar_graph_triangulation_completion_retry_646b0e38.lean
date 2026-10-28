-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_completion_retry_646b0e38
-- name    : WilliamsonShmoys.planar_graph_triangulation_completion_retry_646b0e38
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T14:05:15.900961+00:00
-- url     : https://prove2.me/theorems/d890b646-bb7e-45cb-abf6-d554cf1cf647
-- title:
--   Triangulated completion of a finite planar graph
-- statement:
--   Every finite planar graph on at least three vertices has a planar supergraph on the same vertex set whose edge count is exactly 3 times the number of vertices minus 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_triangulation_completion_retry_646b0e38
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M <= N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V = N.edgeSet.ncard + 6 := by sorry
