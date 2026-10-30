-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_050d6eed_4305_48ca_94b0_9518ffa2e96b_a3
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_050d6eed_4305_48ca_94b0_9518ffa2e96b_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:32:37.353333+00:00
-- url     : https://prove2.me/theorems/46e0438a-7261-453d-aed1-bf3efef6fc1f
-- title:
--   Maximal planar edge count lower bound
-- statement:
--   A drawable simple graph on at least three vertices that admits no drawable strict supergraph on the same vertex type has at least `3|V| - 6` edges. This isolates the work contributed by maximality. A proof route is to show maximality forces connectedness and rules out faces with more than three boundary edges, since a diagonal could be drawn inside such a face to form a drawable supergraph. Triangular faces and Euler's formula then give the lower bound. At three vertices maximality forces the triangle, consistent with the statement. This remains the main triangulation obligation in the reduction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_050d6eed_4305_48ca_94b0_9518ffa2e96b_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hMax : forall H : SimpleGraph V,
      Set.Subset T.edgeSet H.edgeSet ->
      HasPlanarDrawingOn H ->
      Set.Subset H.edgeSet T.edgeSet)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V <= T.edgeSet.ncard + 6 := by
  sorry
