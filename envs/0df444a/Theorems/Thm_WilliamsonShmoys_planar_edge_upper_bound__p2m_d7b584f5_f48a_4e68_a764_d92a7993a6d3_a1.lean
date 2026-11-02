-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_d7b584f5_f48a_4e68_a764_d92a7993a6d3_a1
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_d7b584f5_f48a_4e68_a764_d92a7993a6d3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:40:42.852561+00:00
-- url     : https://prove2.me/theorems/4cf105db-d1e2-4bda-b0a0-c6e9487c258a
-- title:
--   Simple planar edge upper bound
-- statement:
--   Every drawable finite simple graph with at least three vertices has at most three times its vertex count minus six edges. This is the standard planar edge upper bound, obtained from Euler’s formula and the fact that each face boundary has length at least three, with the usual treatment of trees and bridges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_d7b584f5_f48a_4e68_a764_d92a7993a6d3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    L.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
