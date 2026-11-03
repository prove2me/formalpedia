-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_maximal_planar_exact_edge_count__p2m_861504bb_9b69_4346_abcf_17510b6445ad_a1
-- name    : WilliamsonShmoys.planar_edge_bound_for_maximal_planar_exact_edge_count__p2m_861504bb_9b69_4346_abcf_17510b6445ad_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:50:25.458194+00:00
-- url     : https://prove2.me/theorems/4c7ec41a-7a94-4be9-ac1a-23f63e19fba0
-- title:
--   Edge upper bound for a drawable simple graph
-- statement:
--   Any finite drawable simple graph with at least three vertices has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_for_maximal_planar_exact_edge_count__p2m_861504bb_9b69_4346_abcf_17510b6445ad_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     G.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
