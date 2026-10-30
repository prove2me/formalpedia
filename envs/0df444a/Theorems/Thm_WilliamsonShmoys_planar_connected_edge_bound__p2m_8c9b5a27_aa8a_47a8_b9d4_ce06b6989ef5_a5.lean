-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_edge_bound__p2m_8c9b5a27_aa8a_47a8_b9d4_ce06b6989ef5_a5
-- name    : WilliamsonShmoys.planar_connected_edge_bound__p2m_8c9b5a27_aa8a_47a8_b9d4_ce06b6989ef5_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T08:07:02.186002+00:00
-- url     : https://prove2.me/theorems/abe9ada7-d03e-4dfe-be97-61dab793415e
-- title:
--   Edge bound for connected planar drawings
-- statement:
--   A connected finite simple graph with the supplied crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_edge_bound__p2m_8c9b5a27_aa8a_47a8_b9d4_ce06b6989ef5_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hConn : K.Connected)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
