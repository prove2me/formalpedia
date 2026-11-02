-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_55edef6f_d8c2_4514_97bb_024e1dcb6408_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_55edef6f_d8c2_4514_97bb_024e1dcb6408_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:41:00.662222+00:00
-- url     : https://prove2.me/theorems/26140456-b7e4-4d83-b9c1-39ddc27ba139
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph has exactly `3|V| − 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_55edef6f_d8c2_4514_97bb_024e1dcb6408_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N → M ≤ N → N ≤ M) :
    M.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
