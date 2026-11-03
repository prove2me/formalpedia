-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_supergraph__p2m_765f79d2_80fc_4ea0_854a_5bf0163b6a16_a4
-- name    : WilliamsonShmoys.planar_graph_edge_count_supergraph__p2m_765f79d2_80fc_4ea0_854a_5bf0163b6a16_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:03:46.501668+00:00
-- url     : https://prove2.me/theorems/92fbdf79-5590-491f-9884-21ba60b9e74f
-- title:
--   Planar graph is contained in a drawable graph with the maximal planar edge count
-- statement:
--   Every finite drawable simple graph on an ordered vertex type with at least three vertices is contained in a drawable graph on that same vertex type with exactly 3|V|−6 edges. This removes the drawing-extension and planar edge-count work from the parent; the parent uses only containment, drawability, and the edge count. The remaining core is proving the extension and edge-count fact from the supplied crossing-free drawing data.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem WilliamsonShmoys.planar_graph_edge_count_supergraph__p2m_765f79d2_80fc_4ea0_854a_5bf0163b6a16_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
