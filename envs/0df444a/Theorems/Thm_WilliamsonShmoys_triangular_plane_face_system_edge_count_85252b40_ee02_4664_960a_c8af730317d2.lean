-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangular_plane_face_system_edge_count_85252b40_ee02_4664_960a_c8af730317d2
-- name    : WilliamsonShmoys.triangular_plane_face_system_edge_count_85252b40_ee02_4664_960a_c8af730317d2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:15:46.029236+00:00
-- url     : https://prove2.me/theorems/7fc921ae-7dfd-48c2-8fa7-f480759fa132
-- title:
--   Edge count from a triangular plane face system
-- statement:
--   Every finite simple graph with the defined triangular plane face system has exactly 3|V| − 6 edges, expressed as |E| + 6 = 3|V|.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_TriangularPlaneFaceSystem

set_option autoImplicit false

theorem WilliamsonShmoys.triangular_plane_face_system_edge_count_85252b40_ee02_4664_960a_c8af730317d2
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasTriangularPlaneFaceSystem G) :
    G.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
