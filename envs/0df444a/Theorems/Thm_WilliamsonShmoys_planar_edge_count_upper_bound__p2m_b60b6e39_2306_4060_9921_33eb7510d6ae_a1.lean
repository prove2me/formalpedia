-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_b60b6e39_2306_4060_9921_33eb7510d6ae_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_b60b6e39_2306_4060_9921_33eb7510d6ae_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:27:21.277835+00:00
-- url     : https://prove2.me/theorems/1292968f-ac05-4a25-979d-3851b390bd91
-- title:
--   Euler upper bound for drawable graph edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_b60b6e39_2306_4060_9921_33eb7510d6ae_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
