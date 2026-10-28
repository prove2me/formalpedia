-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_bound__p2m_6294dfb9_01c6_44e4_b6a8_a896c7d41add_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_count_bound__p2m_6294dfb9_01c6_44e4_b6a8_a896c7d41add_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:19:59.3465+00:00
-- url     : https://prove2.me/theorems/0ecd79e4-6892-448d-a4b5-6a0f94adcc17
-- title:
--   Edge bound for a finite planar drawing
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most `3|V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_bound__p2m_6294dfb9_01c6_44e4_b6a8_a896c7d41add_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hCard : 3 ≤ Fintype.card V) :
    J.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
