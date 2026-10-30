-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_5ed93e11_5366_47c6_a614_dcb01ec690c9_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_5ed93e11_5366_47c6_a614_dcb01ec690c9_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:35:01.910711+00:00
-- url     : https://prove2.me/theorems/1758d6ea-f3f8-4fd3-af35-9019f186c486
-- title:
--   Edge count of a connected maximal drawable graph
-- statement:
--   A connected, maximal drawable simple graph on at least three vertices has edge count 3|V| − 6, expressed as |E| + 6 = 3|V|.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_5ed93e11_5366_47c6_a614_dcb01ec690c9_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M)
    (hConn : M.Connected)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
