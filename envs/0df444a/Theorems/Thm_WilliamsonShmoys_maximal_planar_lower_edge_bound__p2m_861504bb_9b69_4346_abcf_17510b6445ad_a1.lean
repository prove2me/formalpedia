-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_lower_edge_bound__p2m_861504bb_9b69_4346_abcf_17510b6445ad_a1
-- name    : WilliamsonShmoys.maximal_planar_lower_edge_bound__p2m_861504bb_9b69_4346_abcf_17510b6445ad_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:50:26.584758+00:00
-- url     : https://prove2.me/theorems/0448f4f3-6535-4d82-8dda-cbfbd113fe3f
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal under drawable supergraphs on the same vertex type has at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_lower_edge_bound__p2m_861504bb_9b69_4346_abcf_17510b6445ad_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V,
      G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ G) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     3 * Fintype.card V - 6 ≤ G.edgeFinset.card) := by sorry
