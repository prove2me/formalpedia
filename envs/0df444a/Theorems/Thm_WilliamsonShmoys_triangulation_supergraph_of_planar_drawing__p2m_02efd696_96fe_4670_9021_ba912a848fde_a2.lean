-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulation_supergraph_of_planar_drawing__p2m_02efd696_96fe_4670_9021_ba912a848fde_a2
-- name    : WilliamsonShmoys_triangulation_supergraph_of_planar_drawing__p2m_02efd696_96fe_4670_9021_ba912a848fde_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:43:48.576905+00:00
-- url     : https://prove2.me/theorems/a21b9daf-96c0-42bf-b053-e1966758807a
-- title:
--   Triangulate a connected planar drawing without adding vertices
-- statement:
--   A connected finite simple graph with at least three vertices and a drawing satisfying `HasPlanarDrawingOn` is contained in a graph on the same vertices with such a drawing and exactly `3 * |V| - 6` edges. The statement provides the classical decidable adjacency instance required for the edge-finset expression.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys_triangulation_supergraph_of_planar_drawing__p2m_02efd696_96fe_4670_9021_ba912a848fde_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        (letI : DecidableRel H.Adj := Classical.decRel H.Adj
         H.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
