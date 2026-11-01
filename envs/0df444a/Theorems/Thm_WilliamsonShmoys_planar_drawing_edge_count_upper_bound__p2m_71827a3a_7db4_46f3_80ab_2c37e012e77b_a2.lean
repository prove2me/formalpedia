-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_71827a3a_7db4_46f3_80ab_2c37e012e77b_a2
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_71827a3a_7db4_46f3_80ab_2c37e012e77b_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:57:38.995479+00:00
-- url     : https://prove2.me/theorems/257de7f1-d94a-4116-b7e0-524ede699478
-- title:
--   Planar drawing edge count upper bound
-- statement:
--   Any finite simple graph with a crossing-free drawing and at least three vertices has at most 3n − 6 edges. This removes the upper-bound part of the parent; a proof route is Euler’s formula and face-boundary counting, handling disconnected components by connecting them in the drawing or counting components separately. At n = 3 the bound allows exactly three edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_71827a3a_7db4_46f3_80ab_2c37e012e77b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  sorry
