-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_for_triangulation_extension_v2_0463fea4
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_for_triangulation_extension_v2_0463fea4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T12:04:31.173202+00:00
-- url     : https://prove2.me/theorems/f93c9672-03ce-43e2-94ba-b50b6224a7b6
-- title:
--   Edge count of an edge-maximal drawable graph for the triangulation extension
-- statement:
--   A drawable finite simple graph on at least three vertices that is maximal under drawable edge inclusion has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_for_triangulation_extension_v2_0463fea4
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hmax : ∀ S : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn S →
      Set.Subset R.edgeSet S.edgeSet →
      S.edgeSet = R.edgeSet) :
    R.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
