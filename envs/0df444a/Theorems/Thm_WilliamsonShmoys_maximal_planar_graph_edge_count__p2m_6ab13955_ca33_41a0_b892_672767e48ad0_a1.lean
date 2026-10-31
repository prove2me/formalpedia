-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_6ab13955_ca33_41a0_b892_672767e48ad0_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_6ab13955_ca33_41a0_b892_672767e48ad0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:26:27.274688+00:00
-- url     : https://prove2.me/theorems/19c9eeac-1bda-4675-8c1b-5590acff2ab1
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_6ab13955_ca33_41a0_b892_672767e48ad0_a1 {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V) (hDraw : HasPlanarDrawingOn R) (hV : 3 ≤ Fintype.card V) (hmax : ∀ S : SimpleGraph V, R ≤ S → HasPlanarDrawingOn S → S = R) : R.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
