-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_44b3e4a1_3366_4047_b54d_bdbe1bcd0716_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_44b3e4a1_3366_4047_b54d_bdbe1bcd0716_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:57:59.497015+00:00
-- url     : https://prove2.me/theorems/7d768a9f-2454-410a-aba4-32911cd0fa44
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices with no proper drawable supergraph has exactly 3|V|−6 edges. This is the planar triangulation and Euler-counting step. A proof route is to establish that maximality makes every face triangular, then combine 3F = 2E with Euler’s formula V−E+F = 2. The hypothesis |V| ≥ 3 is necessary for the stated edge-count formula and supplies the boundary range for triangulation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_44b3e4a1_3366_4047_b54d_bdbe1bcd0716_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
