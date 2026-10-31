-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_0e5c0c9f_81d3_4964_a5b1_5841809db03d_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_0e5c0c9f_81d3_4964_a5b1_5841809db03d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:16:19.925276+00:00
-- url     : https://prove2.me/theorems/43e5ee36-822f-4bf9-b718-27a0868cee65
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing on a finite linearly ordered vertex set of at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_0e5c0c9f_81d3_4964_a5b1_5841809db03d_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hMax : ∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = H) (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
