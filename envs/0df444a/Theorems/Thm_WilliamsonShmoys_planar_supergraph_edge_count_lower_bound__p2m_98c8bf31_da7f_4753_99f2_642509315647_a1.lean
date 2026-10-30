-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_lower_bound__p2m_98c8bf31_da7f_4753_99f2_642509315647_a1
-- name    : WilliamsonShmoys.planar_supergraph_edge_count_lower_bound__p2m_98c8bf31_da7f_4753_99f2_642509315647_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T18:37:28.303476+00:00
-- url     : https://prove2.me/theorems/9cc0c9d9-a289-45c0-90c4-3b812fbd190b
-- title:
--   Dense drawable supergraph by triangulation
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertex set with at least 3|V|−6 edges. Connect components and add noncrossing diagonals until the embedding is triangulated; the edge count then gives the bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_edge_count_lower_bound__p2m_98c8bf31_da7f_4753_99f2_642509315647_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      Set.Subset G.edgeSet M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  sorry
