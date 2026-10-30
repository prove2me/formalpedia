-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_upper__p2m_df73036e_c174_45db_bb7e_bf898419f140_a1
-- name    : WilliamsonShmoys_maximal_planar_drawing_edge_count_upper__p2m_df73036e_c174_45db_bb7e_bf898419f140_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-29T23:57:27.052832+00:00
-- url     : https://prove2.me/theorems/3563a5c1-77d2-4f4b-ba7f-85508affa038
-- title:
--   Planar drawing gives the upper edge bound
-- statement:
--   A finite simple graph with the specified crossing-free drawing and at least three vertices has at most 3|V|−6 edges, stated here in natural-number inequality form.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys_maximal_planar_drawing_edge_count_upper__p2m_df73036e_c174_45db_bb7e_bf898419f140_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H) (hCard : 3 ≤ Fintype.card V) : 3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
