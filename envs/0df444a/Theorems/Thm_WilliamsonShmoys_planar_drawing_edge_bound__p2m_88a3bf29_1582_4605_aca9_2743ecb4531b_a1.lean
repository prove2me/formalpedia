-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_88a3bf29_1582_4605_aca9_2743ecb4531b_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_88a3bf29_1582_4605_aca9_2743ecb4531b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:20:32.960671+00:00
-- url     : https://prove2.me/theorems/21c51033-6ced-4e68-8653-efea3430d001
-- title:
--   Planar drawing edge bound
-- statement:
--   Every graph admitting the supplied crossing-free drawing, on at least three vertices, has at most three times its number of vertices minus six edges. The proof route is Euler’s formula for planar embeddings, accounting for disconnected graphs and faces with short boundary walks. This removes the upper-bound half of the target; its core obligation is to formalize the planar Euler bound for this drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_88a3bf29_1582_4605_aca9_2743ecb4531b_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
