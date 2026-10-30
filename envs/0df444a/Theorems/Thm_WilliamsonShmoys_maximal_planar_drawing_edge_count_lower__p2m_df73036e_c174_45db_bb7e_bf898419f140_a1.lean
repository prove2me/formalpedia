-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower__p2m_df73036e_c174_45db_bb7e_bf898419f140_a1
-- name    : WilliamsonShmoys_maximal_planar_drawing_edge_count_lower__p2m_df73036e_c174_45db_bb7e_bf898419f140_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:57:29.30912+00:00
-- url     : https://prove2.me/theorems/ec87327c-94d1-4f33-a35a-c8476e7ad1f3
-- title:
--   Maximality gives the lower edge bound
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least 3|V|−6 edges. A proof route is to show maximality forces a triangulated embedding (or the equivalent Euler face-incidence equations), then combine those equations to obtain the inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys_maximal_planar_drawing_edge_count_lower__p2m_df73036e_c174_45db_bb7e_bf898419f140_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H) (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) (hCard : 3 ≤ Fintype.card V) : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
