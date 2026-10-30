-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_c298a3e1_504a_4c1d_8a31_03ab929cfe86_a2
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c298a3e1_504a_4c1d_8a31_03ab929cfe86_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T08:24:58.809379+00:00
-- url     : https://prove2.me/theorems/b17d3809-e307-4597-82b6-1d4f1ebd7e38
-- title:
--   Planar edge count upper bound
-- statement:
--   A drawable finite simple graph on at least three vertices has at most 3|V|−6 edges, including when it is disconnected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c298a3e1_504a_4c1d_8a31_03ab929cfe86_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hCard : 3 ≤ Fintype.card V) :
    P.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
