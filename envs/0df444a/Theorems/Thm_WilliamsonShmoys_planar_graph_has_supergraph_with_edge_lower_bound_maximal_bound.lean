-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_supergraph_with_edge_lower_bound_maximal_bound
-- name    : WilliamsonShmoys.planar_graph_has_supergraph_with_edge_lower_bound_maximal_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T02:03:20.055186+00:00
-- url     : https://prove2.me/theorems/1be85767-9b5d-4964-823c-ae4014c87c51
-- title:
--   Maximal drawable graphs satisfy the planar edge bound
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph on the same vertices has at least 3|V|−6 edges. A proof route establishes that maximality forces triangular faces in a plane embedding, then applies Euler’s formula and counts face-edge incidences. The hypotheses retain the needed lower bound on the vertex count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_supergraph_with_edge_lower_bound_maximal_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hMax : ∀ W : SimpleGraph V,
      Z ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W ≤ Z) :
    3 * Fintype.card V ≤ Z.edgeSet.ncard + 6 := by sorry
