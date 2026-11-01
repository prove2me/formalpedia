-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_0d2111fe_49a0_4983_b8b9_46fbb1acc127_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_0d2111fe_49a0_4983_b8b9_46fbb1acc127_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:04:38.241248+00:00
-- url     : https://prove2.me/theorems/53a59b51-a27a-49a5-8afe-47c450cb8c81
-- title:
--   Planar edge count upper bound
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. The hypothesis covers the small boundary case where the standard planar Euler edge bound begins; it also permits disconnected graphs. The proof route is to derive Euler’s formula for the drawing, then use simplicity to bound face boundary lengths below by three (with the usual treatment of components and bridges). This removes the universal planar edge-count argument from the parent. The remaining core obligation is formalizing the Euler and face-boundary arguments from the explicit drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_0d2111fe_49a0_4983_b8b9_46fbb1acc127_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
