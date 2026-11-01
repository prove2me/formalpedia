-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_has_euler_edge_count__p2m_9c07cfc8_fca3_44bb_9466_8248a8f68ed4_a1
-- name    : WilliamsonShmoys.edge_maximal_planar_has_euler_edge_count__p2m_9c07cfc8_fca3_44bb_9466_8248a8f68ed4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:05:41.61511+00:00
-- url     : https://prove2.me/theorems/24bfc568-7b25-4409-b2ae-c59e72f324da
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A drawable finite simple graph on at least three vertices that is maximal under drawable supergraphs has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.edge_maximal_planar_has_euler_edge_count__p2m_9c07cfc8_fca3_44bb_9466_8248a8f68ed4_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) : 3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  sorry
