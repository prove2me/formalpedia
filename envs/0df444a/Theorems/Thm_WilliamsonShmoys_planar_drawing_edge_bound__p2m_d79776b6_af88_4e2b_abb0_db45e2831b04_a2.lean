-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_d79776b6_af88_4e2b_abb0_db45e2831b04_a2
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_d79776b6_af88_4e2b_abb0_db45e2831b04_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:50:47.982388+00:00
-- url     : https://prove2.me/theorems/658fbae2-a8f1-4378-a350-5dcdadc787bf
-- title:
--   Euler edge bound for a connected planar drawing
-- statement:
--   Every finite connected simple graph with at least three vertices and a drawing satisfying WilliamsonShmoys.HasPlanarDrawingOn has at most 3|V| − 6 edges. The vertex lower bound includes the three-vertex boundary case; connectedness is needed for the Euler-formula route.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_d79776b6_af88_4e2b_abb0_db45e2831b04_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
