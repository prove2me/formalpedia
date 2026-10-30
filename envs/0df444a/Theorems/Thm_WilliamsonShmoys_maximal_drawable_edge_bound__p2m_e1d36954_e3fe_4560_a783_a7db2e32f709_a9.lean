-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_bound__p2m_e1d36954_e3fe_4560_a783_a7db2e32f709_a9
-- name    : WilliamsonShmoys.maximal_drawable_edge_bound__p2m_e1d36954_e3fe_4560_a783_a7db2e32f709_a9
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:26:00.104001+00:00
-- url     : https://prove2.me/theorems/3d56d8a6-4977-48bc-b3fc-35028523ea34
-- title:
--   Edge bound for an edge-maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices whose drawable supergraphs never have more edges satisfies the planar edge-count bound. The parent selects such a graph by maximizing edge count over the finite family of drawable supergraphs of the input graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_bound__p2m_e1d36954_e3fe_4560_a783_a7db2e32f709_a9
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet.ncard ≤ M.edgeSet.ncard) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  sorry
