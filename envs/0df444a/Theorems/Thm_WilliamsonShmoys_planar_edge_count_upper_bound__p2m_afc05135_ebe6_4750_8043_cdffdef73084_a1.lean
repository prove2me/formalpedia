-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_afc05135_ebe6_4750_8043_cdffdef73084_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_afc05135_ebe6_4750_8043_cdffdef73084_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:52:43.141407+00:00
-- url     : https://prove2.me/theorems/20a1c1d8-1bb0-41df-b55c-0fe6ecae9409
-- title:
--   Planar edge count upper bound
-- statement:
--   For a finite simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn, its edge count is at most 3 times the number of vertices minus 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_afc05135_ebe6_4750_8043_cdffdef73084_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
