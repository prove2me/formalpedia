-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_count__p2m_82e54da5_16cf_4d16_b293_9f40ba57f2f4_a3
-- name    : WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_82e54da5_16cf_4d16_b293_9f40ba57f2f4_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:52:43.005208+00:00
-- url     : https://prove2.me/theorems/b320f89e-6adf-4c95-8da8-b179076388d4
-- title:
--   Planar completion with the triangulation edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. This removes the geometric completion, triangulation, and Euler-counting work from the parent. A proof route is to extend the drawing to a maximal planar graph, connect components as necessary, show that maximality forces triangular faces, and count with Euler’s formula. For three vertices the completion is K₃. The parent uses maximality to identify the completion with the original graph. The remaining core obligation is proving this topological completion and counting result.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_82e54da5_16cf_4d16_b293_9f40ba57f2f4_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V) :
    exists N : SimpleGraph V,
      M <= N /\
      WilliamsonShmoys.HasPlanarDrawingOn N /\
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
