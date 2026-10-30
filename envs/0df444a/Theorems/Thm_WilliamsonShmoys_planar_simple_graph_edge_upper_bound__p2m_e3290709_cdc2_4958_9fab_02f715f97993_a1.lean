-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_e3290709_cdc2_4958_9fab_02f715f97993_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_e3290709_cdc2_4958_9fab_02f715f97993_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:37:36.946984+00:00
-- url     : https://prove2.me/theorems/d64d875f-ca91-4b99-90b7-6f6b1ae2c52d
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every finite simple graph with a drawing satisfying `HasPlanarDrawingOn` and at least three vertices has at most `3n - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_e3290709_cdc2_4958_9fab_02f715f97993_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
