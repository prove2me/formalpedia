-- Prove2me | Theorems.Thm_WilliamsonShmoys_has_planar_drawing_on_edge_count_le_three_card_sub_six
-- name    : WilliamsonShmoys.has_planar_drawing_on_edge_count_le_three_card_sub_six
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:58:51.218966+00:00
-- url     : https://prove2.me/theorems/caf89453-fefb-49cf-ad04-ba4468da8e18
-- title:
--   Planar drawing edge count bound
-- statement:
--   A finite simple graph with at least three vertices and a crossing-free drawing has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.has_planar_drawing_on_edge_count_le_three_card_sub_six {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V) : G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
