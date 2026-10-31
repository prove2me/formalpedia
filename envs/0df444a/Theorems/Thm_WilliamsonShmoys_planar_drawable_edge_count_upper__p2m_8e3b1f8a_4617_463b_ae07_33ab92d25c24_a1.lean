-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_edge_count_upper__p2m_8e3b1f8a_4617_463b_ae07_33ab92d25c24_a1
-- name    : WilliamsonShmoys.planar_drawable_edge_count_upper__p2m_8e3b1f8a_4617_463b_ae07_33ab92d25c24_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:51:19.091986+00:00
-- url     : https://prove2.me/theorems/12739147-2229-46d9-9b92-e1d48da872e9
-- title:
--   Upper edge-count bound for a drawable simple graph
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawable_edge_count_upper__p2m_8e3b1f8a_4617_463b_ae07_33ab92d25c24_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G) (hCard : 3 <= Fintype.card V) : G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
