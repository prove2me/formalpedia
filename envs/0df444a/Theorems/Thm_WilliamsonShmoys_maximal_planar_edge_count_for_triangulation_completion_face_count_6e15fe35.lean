-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_triangulation_completion_face_count_6e15fe35
-- name    : WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_completion_face_count_6e15fe35
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:49:08.774293+00:00
-- url     : https://prove2.me/theorems/ecb5846b-8bbc-4ac2-9f39-72be3e0cd9f0
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A finite simple graph with at least three vertices that is maximal among graphs admitting the specified crossing-free drawing has exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_completion_face_count_6e15fe35
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → M = N)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
