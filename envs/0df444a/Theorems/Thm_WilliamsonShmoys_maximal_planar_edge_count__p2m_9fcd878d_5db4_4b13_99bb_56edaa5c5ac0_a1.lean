-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_9fcd878d_5db4_4b13_99bb_56edaa5c5ac0_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_9fcd878d_5db4_4b13_99bb_56edaa5c5ac0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:59:39.617213+00:00
-- url     : https://prove2.me/theorems/0d2111fe-49a0-4983-b8b9-46fbb1acc127
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   An inclusion-maximal finite simple planar graph on at least three vertices has exactly 3|V|−6 edges. This removes the planar embedding and Euler-formula argument from the parent. A proof route is to show every face in a maximal planar embedding is a triangle, and then apply Euler’s formula; the at-least-three-vertices hypothesis covers the smallest triangulation, K₃.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_9fcd878d_5db4_4b13_99bb_56edaa5c5ac0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hMax : ∀ (P : SimpleGraph V),
      (∀ u v, G.Adj u v → P.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn P → P = G)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = G.edgeSet.ncard + 6 := by sorry
