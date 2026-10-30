-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_dbab630e_c01d_4b47_9ab6_dd56c8211fc8_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_dbab630e_c01d_4b47_9ab6_dd56c8211fc8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T08:45:51.653018+00:00
-- url     : https://prove2.me/theorems/4c27668b-2681-4160-a7ae-a19f29ed8ce0
-- title:
--   Edge bound for a simple planar drawing
-- statement:
--   A finite simple graph with the specified planar drawing and at least three vertices has at most 3V − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_dbab630e_c01d_4b47_9ab6_dd56c8211fc8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hConn : K.Connected)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
