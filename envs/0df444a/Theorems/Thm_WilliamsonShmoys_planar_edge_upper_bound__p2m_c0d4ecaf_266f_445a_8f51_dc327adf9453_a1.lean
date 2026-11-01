-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_c0d4ecaf_266f_445a_8f51_dc327adf9453_a1
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_c0d4ecaf_266f_445a_8f51_dc327adf9453_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:25:41.791212+00:00
-- url     : https://prove2.me/theorems/c52ee0f6-cd77-40cf-a2f0-4d029ef0159f
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_c0d4ecaf_266f_445a_8f51_dc327adf9453_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
