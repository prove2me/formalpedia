-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_for_edge_bound__p2m_55c0bceb_ffb6_44c6_a362_90e494710496_a2
-- name    : WilliamsonShmoys.maximal_planar_completion_for_edge_bound__p2m_55c0bceb_ffb6_44c6_a362_90e494710496_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:31:13.427393+00:00
-- url     : https://prove2.me/theorems/7421bb86-5406-4559-80b0-0937bd98493b
-- title:
--   Maximal drawable supergraph on the same vertices
-- statement:
--   Every drawable finite simple graph on the fixed vertex type is contained in an inclusion-maximal drawable supergraph, with its edge count no larger than the supergraph’s.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_completion_for_edge_bound__p2m_55c0bceb_ffb6_44c6_a362_90e494710496_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ M : SimpleGraph V,
      H ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       letI : DecidableRel M.Adj := Classical.decRel M.Adj
       H.edgeFinset.card ≤ M.edgeFinset.card) := by sorry
