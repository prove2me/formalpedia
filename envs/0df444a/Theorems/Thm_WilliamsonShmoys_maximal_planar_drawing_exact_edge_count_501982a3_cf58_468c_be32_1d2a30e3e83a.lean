-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count_501982a3_cf58_468c_be32_1d2a30e3e83a
-- name    : WilliamsonShmoys.maximal_planar_drawing_exact_edge_count_501982a3_cf58_468c_be32_1d2a30e3e83a
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T02:27:19.941305+00:00
-- url     : https://prove2.me/theorems/a76877fd-7551-4249-899d-5acc3f351e6a
-- title:
--   Exact edge count for maximal planar drawings
-- statement:
--   A maximal graph with a crossing-free drawing on at least three vertices has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_exact_edge_count_501982a3_cf58_468c_be32_1d2a30e3e83a
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V, N ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
