-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_1df68e30_02cf_4572_bf8a_d78917d2b48a_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_1df68e30_02cf_4572_bf8a_d78917d2b48a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:01:44.677355+00:00
-- url     : https://prove2.me/theorems/fd05939c-3060-4687-b686-08bcaa4f6cdd
-- title:
--   Planar drawing edge upper bound
-- statement:
--   Any simple graph on at least three vertices with a drawing satisfying the supplied crossing-free drawing predicate has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_1df68e30_02cf_4572_bf8a_d78917d2b48a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
