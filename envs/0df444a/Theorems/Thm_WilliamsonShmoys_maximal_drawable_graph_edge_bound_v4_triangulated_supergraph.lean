-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_bound_v4_triangulated_supergraph
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_bound_v4_triangulated_supergraph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T04:50:33.969449+00:00
-- url     : https://prove2.me/theorems/0c9f4ecf-e48c-41a7-930a-efceb2c0f3bf
-- title:
--   A drawable graph extends to a triangulated planar graph
-- statement:
--   Every finite drawable simple graph on at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges. This is the augmentation-to-triangulation step; the exact edge count follows from Euler’s formula once the augmentation is shown to have triangular faces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_bound_v4_triangulated_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      (N.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
