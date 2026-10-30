-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_43e5ee36_822f_4bf9_b718_27a0868cee65_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_43e5ee36_822f_4bf9_b718_27a0868cee65_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:21:48.14605+00:00
-- url     : https://prove2.me/theorems/02b7676f-a513-46e6-8e4a-f3d718372bb1
-- title:
--   Lower edge bound for maximal planar graphs
-- statement:
--   A maximal graph with a crossing-free drawing and at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_43e5ee36_822f_4bf9_b718_27a0868cee65_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hMax : ∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = H) (hV : 3 ≤ Fintype.card V) : 3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by sorry
