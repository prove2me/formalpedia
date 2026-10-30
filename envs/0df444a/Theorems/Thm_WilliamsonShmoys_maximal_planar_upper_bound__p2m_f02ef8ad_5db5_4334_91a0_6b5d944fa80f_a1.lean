-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_upper_bound__p2m_f02ef8ad_5db5_4334_91a0_6b5d944fa80f_a1
-- name    : WilliamsonShmoys.maximal_planar_upper_bound__p2m_f02ef8ad_5db5_4334_91a0_6b5d944fa80f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T12:06:12.467934+00:00
-- url     : https://prove2.me/theorems/11b8d141-5db8-4e85-8178-19adf7dd7abd
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_upper_bound__p2m_f02ef8ad_5db5_4334_91a0_6b5d944fa80f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
