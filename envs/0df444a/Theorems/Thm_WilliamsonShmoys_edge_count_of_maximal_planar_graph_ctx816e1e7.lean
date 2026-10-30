-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_graph_ctx816e1e7
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_graph_ctx816e1e7
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:16:22.815975+00:00
-- url     : https://prove2.me/theorems/fd139372-78d9-4e18-bb68-2df73fbb427d
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An inclusion-maximal drawable simple graph on a finite linearly ordered vertex type with at least three vertices has exactly 3|V| − 6 edges. Maximality rules out disconnected or nontriangular planar regions that could accept another edge; the resulting triangulation edge count follows from Euler’s formula. The three-vertex case is the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_maximal_planar_graph_ctx816e1e7
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hmax : ∀ S : SimpleGraph V, R ≤ S →
      WilliamsonShmoys.HasPlanarDrawingOn S → S ≤ R) :
    R.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
