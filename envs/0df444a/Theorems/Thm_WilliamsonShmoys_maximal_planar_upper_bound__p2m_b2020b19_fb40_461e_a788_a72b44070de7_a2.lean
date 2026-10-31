-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_upper_bound__p2m_b2020b19_fb40_461e_a788_a72b44070de7_a2
-- name    : WilliamsonShmoys.maximal_planar_upper_bound__p2m_b2020b19_fb40_461e_a788_a72b44070de7_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T18:29:59.41734+00:00
-- url     : https://prove2.me/theorems/212795a8-c633-43e2-bc24-6d65a9f436cf
-- title:
--   Euler upper bound for a drawable simple graph
-- statement:
--   Every drawable finite simple graph with at least three vertices has at most three times its number of vertices minus six edges. This is the Euler-counting half of the target and applies whether or not the graph is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_upper_bound__p2m_b2020b19_fb40_461e_a788_a72b44070de7_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
