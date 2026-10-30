-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_has_triangulated_edge_count_for_bound_2eec570b_ffd5_435e_a8fa_d87718384d1c
-- name    : WilliamsonShmoys.edge_maximal_planar_graph_has_triangulated_edge_count_for_bound_2eec570b_ffd5_435e_a8fa_d87718384d1c
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:13:09.373558+00:00
-- url     : https://prove2.me/theorems/b74e21e6-3fc1-461f-9f0a-f16337c283e8
-- title:
--   Maximal drawable graph has the triangulation edge count for this bound
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs has exactly 3|V| − 6 edges. This child removes the topological and Euler-counting core from the parent. A proof route is to represent the drawing as a plane embedding, use maximality to show the embedding is connected and every face is a triangle (otherwise add an edge inside a face), and apply Euler’s formula and the count of face-edge incidences. The hypothesis |V| ≥ 3 is essential to the formula; the boundary case |V| = 3 gives the triangle. This remains the central unproved obligation of the reduction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_graph_has_triangulated_edge_count_for_bound_2eec570b_ffd5_435e_a8fa_d87718384d1c
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet ⊆ H.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
