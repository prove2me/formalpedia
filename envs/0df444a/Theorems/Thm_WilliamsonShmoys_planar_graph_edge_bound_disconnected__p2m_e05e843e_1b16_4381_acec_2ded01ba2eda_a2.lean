-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_bound_disconnected__p2m_e05e843e_1b16_4381_acec_2ded01ba2eda_a2
-- name    : WilliamsonShmoys.planar_graph_edge_bound_disconnected__p2m_e05e843e_1b16_4381_acec_2ded01ba2eda_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:06:22.196595+00:00
-- url     : https://prove2.me/theorems/412cf563-cd90-4618-ba6d-11be264b4659
-- title:
--   Edge bound for a disconnected finite planar graph
-- statement:
--   A disconnected finite simple graph with at least three vertices and a crossing-free drawing satisfies the planar edge bound. Restrict the drawing to each connected component, use the connected estimate on components with at least three vertices, bound the one- and two-vertex components directly, and sum the component edge counts.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_edge_bound_disconnected__p2m_e05e843e_1b16_4381_acec_2ded01ba2eda_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : ¬ H.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
