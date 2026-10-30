-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_on_fixed_vertex_type_4156f0d3
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_on_fixed_vertex_type_4156f0d3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:55:36.584663+00:00
-- url     : https://prove2.me/theorems/aea3a4e2-bf3e-4b3e-858c-45991cf7934b
-- title:
--   Edge count of a maximal drawable graph on the fixed vertex type
-- statement:
--   A drawable finite simple graph on at least three vertices that is inclusion maximal among drawable supergraphs on the same vertex type has exactly `3|V|−6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_on_fixed_vertex_type_4156f0d3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, Set.Subset H.edgeSet K.edgeSet →
      HasPlanarDrawingOn K → Set.Subset K.edgeSet H.edgeSet) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
