-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_edge_count_upper_bound__p2m_2a3bf938_54d7_4ba6_ba97_85998ae61b74_a4
-- name    : WilliamsonShmoys.planar_drawing_connected_edge_count_upper_bound__p2m_2a3bf938_54d7_4ba6_ba97_85998ae61b74_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T05:24:09.394992+00:00
-- url     : https://prove2.me/theorems/f79a538d-f02a-4fcf-b5f6-4cc482860df4
-- title:
--   Connected planar drawing edge-count bound
-- statement:
--   A connected finite simple graph with the specified crossing-free drawing and at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_edge_count_upper_bound__p2m_2a3bf938_54d7_4ba6_ba97_85998ae61b74_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hConnected : L.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
