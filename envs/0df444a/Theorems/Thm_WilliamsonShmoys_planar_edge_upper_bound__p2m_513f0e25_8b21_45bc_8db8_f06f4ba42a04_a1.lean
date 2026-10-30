-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_513f0e25_8b21_45bc_8db8_f06f4ba42a04_a1
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_513f0e25_8b21_45bc_8db8_f06f4ba42a04_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T08:31:02.509992+00:00
-- url     : https://prove2.me/theorems/6d696f5c-d0ea-417d-ad76-7240c2701de0
-- title:
--   Euler upper bound for a finite simple planar graph
-- statement:
--   Every graph satisfying the supplied crossing-free drawing predicate on at least three vertices has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_513f0e25_8b21_45bc_8db8_f06f4ba42a04_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
