-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_edge_count__p2m_4c7ec41a_7a94_4be9_ac1a_23f63e19fba0_a1
-- name    : WilliamsonShmoys.planar_supergraph_triangulation_edge_count__p2m_4c7ec41a_7a94_4be9_ac1a_23f63e19fba0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:55:35.745094+00:00
-- url     : https://prove2.me/theorems/d9484fdc-deb9-4095-abe2-5d54d805080e
-- title:
--   Triangulated planar supergraph with the maximal edge count
-- statement:
--   Every finite simple graph with at least three vertices that has a crossing-free drawing is contained, on the same vertex set, in a drawable simple graph with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_triangulation_edge_count__p2m_4c7ec41a_7a94_4be9_ac1a_23f63e19fba0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        (letI : DecidableRel H.Adj := Classical.decRel H.Adj
         H.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
