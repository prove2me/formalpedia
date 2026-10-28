-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_supergraph_with_edge_lower_bound_completion
-- name    : WilliamsonShmoys.planar_graph_has_supergraph_with_edge_lower_bound_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:57:39.745993+00:00
-- url     : https://prove2.me/theorems/487640ed-9f32-4651-8051-6f35d2394c21
-- title:
--   Extend to a maximal drawable supergraph
-- statement:
--   Extend the input graph to a drawable supergraph on the same finite vertex type that is maximal among drawable supergraphs under graph inclusion. The boundary case of three vertices is permitted. A proof route is to maximize edge count over the finite set of simple graphs containing the input that admit a drawing; any drawable extension then has no additional edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_supergraph_with_edge_lower_bound_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ Z : SimpleGraph V,
      Y ≤ Z ∧
      WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      (∀ W : SimpleGraph V,
        Z ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W ≤ Z) := by sorry
