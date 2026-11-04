-- Prove2me | Theorems.Thm_drawable_graph_edge_bound__p2m_d1879139_c8f2_40b8_b730_a1c2d5f0f3db_a2
-- name    : drawable_graph_edge_bound__p2m_d1879139_c8f2_40b8_b730_a1c2d5f0f3db_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:03:54.905206+00:00
-- url     : https://prove2.me/theorems/165ee858-132c-470d-9b30-10e365098e80
-- title:
--   Edge bound for a drawable graph
-- statement:
--   A drawable simple graph on at least three finite, linearly ordered vertices has at most three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem drawable_graph_edge_bound__p2m_d1879139_c8f2_40b8_b730_a1c2d5f0f3db_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hn : 3 ≤ Fintype.card V) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
