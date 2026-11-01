-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_completion__p2m_9c07cfc8_fca3_44bb_9466_8248a8f68ed4_a1
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_completion__p2m_9c07cfc8_fca3_44bb_9466_8248a8f68ed4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:05:38.422338+00:00
-- url     : https://prove2.me/theorems/99f498ba-8796-40c9-a103-6d7b97940db4
-- title:
--   Existence of an edge-maximal planar completion
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex set that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_edge_maximal_planar_completion__p2m_9c07cfc8_fca3_44bb_9466_8248a8f68ed4_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) : ∃ M' : SimpleGraph V, M ≤ M' ∧ WilliamsonShmoys.HasPlanarDrawingOn M' ∧ ∀ N : SimpleGraph V, M' ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M' := by
  sorry
