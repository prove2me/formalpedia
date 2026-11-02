-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_3ea1a2df_ff39_4335_a398_1933022707b1_a2
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_3ea1a2df_ff39_4335_a398_1933022707b1_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:42:56.489539+00:00
-- url     : https://prove2.me/theorems/b05574a0-b431-4a4f-aba2-4718b07b1171
-- title:
--   Finite maximal drawable supergraph with edge monotonicity
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is inclusion-maximal among drawable supergraphs and has at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_3ea1a2df_ff39_4335_a398_1933022707b1_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ M : SimpleGraph V,
      H ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       letI : DecidableRel M.Adj := Classical.decRel M.Adj
       H.edgeFinset.card ≤ M.edgeFinset.card) ∧
      (∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) := by sorry
