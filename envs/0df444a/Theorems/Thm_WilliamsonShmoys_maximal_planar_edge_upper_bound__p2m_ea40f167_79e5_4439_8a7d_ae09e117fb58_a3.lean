-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_upper_bound__p2m_ea40f167_79e5_4439_8a7d_ae09e117fb58_a3
-- name    : WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_ea40f167_79e5_4439_8a7d_ae09e117fb58_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:24:03.573795+00:00
-- url     : https://prove2.me/theorems/ca990ca2-90e1-475e-969d-4e2c10201187
-- title:
--   Edge upper bound for a finite simple planar graph
-- statement:
--   Every drawable finite simple graph with at least three vertices has at most 3n − 6 edges. This supplies the upper bound needed for equality in the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_ea40f167_79e5_4439_8a7d_ae09e117fb58_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
