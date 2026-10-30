-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_upper_bound__p2m_648e2563_4933_48d5_af68_a43e4e82ab0d_a1
-- name    : WilliamsonShmoys.planar_graph_edge_upper_bound__p2m_648e2563_4933_48d5_af68_a43e4e82ab0d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:26:41.858757+00:00
-- url     : https://prove2.me/theorems/a6e6652d-e481-443f-9c79-230fd6c973a0
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_edge_upper_bound__p2m_648e2563_4933_48d5_af68_a43e4e82ab0d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
