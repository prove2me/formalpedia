-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_formula
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_formula
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T20:07:37.64314+00:00
-- url     : https://prove2.me/theorems/82ef3aa2-e16a-4b8d-a817-210f6925d36e
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_graph_edge_formula
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hMax : ∀ S : SimpleGraph V, R ≤ S →
      WilliamsonShmoys.HasPlanarDrawingOn S → S = R) :
    R.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
