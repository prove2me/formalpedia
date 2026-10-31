-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_fbd4abfa_95e6_415e_91e9_eb5757f71c9a_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_fbd4abfa_95e6_415e_91e9_eb5757f71c9a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:11:18.594987+00:00
-- url     : https://prove2.me/theorems/c2c1b3a4-fb5c-4278-a971-04a8ba2bc900
-- title:
--   Euler edge bound for a finite planar drawing
-- statement:
--   Any finite simple graph with the given crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This is the Euler-formula upper-bound step; the threshold n≥3 is needed for the bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_fbd4abfa_95e6_415e_91e9_eb5757f71c9a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
