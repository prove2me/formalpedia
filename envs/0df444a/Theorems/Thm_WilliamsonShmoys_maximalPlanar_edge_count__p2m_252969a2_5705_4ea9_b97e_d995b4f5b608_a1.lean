-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximalPlanar_edge_count__p2m_252969a2_5705_4ea9_b97e_d995b4f5b608_a1
-- name    : WilliamsonShmoys.maximalPlanar_edge_count__p2m_252969a2_5705_4ea9_b97e_d995b4f5b608_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:54:16.822756+00:00
-- url     : https://prove2.me/theorems/7a0d3f25-089a-4d82-a9d5-85ef68cd5f10
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An inclusion-maximal graph admitting the supplied crossing-free drawing on a finite vertex type with at least three vertices has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximalPlanar_edge_count__p2m_252969a2_5705_4ea9_b97e_d995b4f5b608_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) (hV : 3 ≤ Fintype.card V) : M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
