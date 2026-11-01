-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation__p2m_257de7f1_d94a_4116_b7e0_524ede699478_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_257de7f1_d94a_4116_b7e0_524ede699478_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T02:07:19.186143+00:00
-- url     : https://prove2.me/theorems/5897f64b-d93f-46d0-b145-4fa00606e1c1
-- title:
--   Connect components of a planar drawing without losing edges
-- statement:
--   Any finite simple graph with a crossing-free drawing can be extended on the same vertex type to a connected graph with a crossing-free drawing, without decreasing its number of edges. This isolates the disconnected-component bookkeeping needed by the parent. A proof route is to connect drawing components successively by arcs through the complement of the finite embedded graph, then preserve all original edges. The parent uses only the resulting edge-count monotonicity and connectedness. The geometric extension argument remains to be formalized.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_257de7f1_d94a_4116_b7e0_524ede699478_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected ∧
      M.edgeSet.ncard ≤ H.edgeSet.ncard := by
  sorry
