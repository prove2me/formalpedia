-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_drawing_connected__p2m_bfb48bad_a912_467d_9a83_873a376cfdde_a1
-- name    : WilliamsonShmoys.planar_edge_bound_of_drawing_connected__p2m_bfb48bad_a912_467d_9a83_873a376cfdde_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:39:15.212439+00:00
-- url     : https://prove2.me/theorems/e9cc7ebe-a4b1-46c5-abf0-9e9356d8afb2
-- title:
--   Euler edge bound for a connected graph with a planar drawing
-- statement:
--   A finite simple graph with a crossing-free drawing, which is connected and has at least three vertices, has at most three times its vertex count minus six edges. The proof formalizes Euler's formula for the embedding and counts edge incidences on face boundaries.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_of_drawing_connected__p2m_bfb48bad_a912_467d_9a83_873a376cfdde_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
