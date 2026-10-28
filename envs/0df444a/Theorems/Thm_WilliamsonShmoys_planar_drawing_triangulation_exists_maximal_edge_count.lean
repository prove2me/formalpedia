-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_exists_maximal_edge_count
-- name    : WilliamsonShmoys.planar_drawing_triangulation_exists_maximal_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T22:13:08.59986+00:00
-- url     : https://prove2.me/theorems/2b8a4e88-7079-4f1d-bf60-1d10da386ed9
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices with no strictly larger drawable supergraph on the same vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_exists_maximal_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
