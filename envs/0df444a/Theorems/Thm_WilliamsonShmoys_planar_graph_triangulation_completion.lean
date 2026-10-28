-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_completion
-- name    : WilliamsonShmoys.planar_graph_triangulation_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T02:29:52.147024+00:00
-- url     : https://prove2.me/theorems/7bb4f585-9598-4e28-badb-ea1bb910d7fc
-- title:
--   Completion of a planar drawing to a triangulation
-- statement:
--   Every graph with a crossing-free drawing on at least three vertices has a drawable supergraph on the same vertices whose edge count is exactly three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_triangulation_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
