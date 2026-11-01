-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_0d2111fe_49a0_4983_b8b9_46fbb1acc127_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_0d2111fe_49a0_4983_b8b9_46fbb1acc127_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:04:40.033335+00:00
-- url     : https://prove2.me/theorems/ab59570c-fffd-4137-a2d3-71557bc91725
-- title:
--   Maximal planar edge count lower bound
-- statement:
--   An inclusion-maximal finite simple planar graph on at least three vertices has at least 3|V|−6 edges. Given a planar drawing, extend the graph on the same vertex set to a triangulation; the extension contains every edge of G and remains drawable, so the maximality hypothesis forces it to equal G. Counting the triangulation’s triangular faces with Euler’s formula gives the inequality. The at-least-three hypothesis preserves the `K₃` boundary case. This removes the maximality-to-triangulation argument from the parent. The remaining core obligation is establishing a triangulating extension for the explicit drawing convention and formalizing its face count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_0d2111fe_49a0_4983_b8b9_46fbb1acc127_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hMax : ∀ (P : SimpleGraph V),
      (∀ u v, G.Adj u v → P.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn P → P = G)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by sorry
