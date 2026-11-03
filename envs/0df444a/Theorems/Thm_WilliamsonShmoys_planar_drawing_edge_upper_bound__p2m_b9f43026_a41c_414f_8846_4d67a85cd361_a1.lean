-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_b9f43026_a41c_414f_8846_4d67a85cd361_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_b9f43026_a41c_414f_8846_4d67a85cd361_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:43:15.668129+00:00
-- url     : https://prove2.me/theorems/9fddd72b-ea70-4f6e-a8cc-a62e654b4dbf
-- title:
--   Simple planar drawing edge upper bound
-- statement:
--   Every simple graph on at least three vertices with the specified crossing-free drawing has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_b9f43026_a41c_414f_8846_4d67a85cd361_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hCard : 3 <= Fintype.card V) : G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
