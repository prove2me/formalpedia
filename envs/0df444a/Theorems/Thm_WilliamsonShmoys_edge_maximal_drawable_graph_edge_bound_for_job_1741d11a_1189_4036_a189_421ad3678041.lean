-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_drawable_graph_edge_bound_for_job_1741d11a_1189_4036_a189_421ad3678041
-- name    : WilliamsonShmoys.edge_maximal_drawable_graph_edge_bound_for_job_1741d11a_1189_4036_a189_421ad3678041
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T05:48:03.191314+00:00
-- url     : https://prove2.me/theorems/057ef142-41f3-41d0-8648-8115a105ce61
-- title:
--   An edge-maximal drawable graph has the planar lower edge bound
-- statement:
--   A drawable graph on at least three vertices that has no strict drawable supergraph on the same vertices has at least 3|V| − 6 edges. The hypothesis |V| ≥ 3 is preserved because the edge bound is not asserted for smaller orders. A proof route is to show maximality forces a connected triangulated embedding and then use Euler’s formula and face-edge counting. This isolates the topology and counting argument as the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_drawable_graph_edge_bound_for_job_1741d11a_1189_4036_a189_421ad3678041
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N →
      Set.Subset M.edgeSet N.edgeSet →
      Set.Subset N.edgeSet M.edgeSet)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by sorry
