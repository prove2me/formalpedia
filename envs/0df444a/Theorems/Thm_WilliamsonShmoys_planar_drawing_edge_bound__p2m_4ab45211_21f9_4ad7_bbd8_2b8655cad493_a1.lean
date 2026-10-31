-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_4ab45211_21f9_4ad7_bbd8_2b8655cad493_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_4ab45211_21f9_4ad7_bbd8_2b8655cad493_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T06:23:54.261586+00:00
-- url     : https://prove2.me/theorems/dd51b18f-7df2-4399-b7a3-088f0da934ea
-- title:
--   Edge bound for a graph with a planar drawing
-- statement:
--   Any finite simple graph with a drawing satisfying `HasPlanarDrawingOn` has at most `3|V|−6` edges, expressed in the equivalent form `3|V| ≤ |E|+6`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_4ab45211_21f9_4ad7_bbd8_2b8655cad493_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G) : 3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by sorry
