-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_completion_for_edge_count
-- name    : WilliamsonShmoys.planar_graph_has_triangulated_completion_for_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T18:47:53.607536+00:00
-- url     : https://prove2.me/theorems/19818e22-2386-49d7-851c-0c578cd76de2
-- title:
--   Planar completion with the maximal edge count
-- statement:
--   Every drawable graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges. This is the planar completion fact needed by the parent; its proof must handle disconnected graphs and the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_triangulated_completion_for_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
