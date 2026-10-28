-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_maximal_supergraph_for_triangulated_edge_count_bound_2eec570b_ffd5_435e_a8fa_d87718384d1c
-- name    : WilliamsonShmoys.planar_drawing_has_edge_maximal_supergraph_for_triangulated_edge_count_bound_2eec570b_ffd5_435e_a8fa_d87718384d1c
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:04:55.328906+00:00
-- url     : https://prove2.me/theorems/bf41acef-db6f-4a02-bff4-c1b8c16181b6
-- title:
--   Drawable graph has a maximal drawable extension for the edge-count bound
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal by edge inclusion among drawable supergraphs. The claim has no lower bound on the number of vertices. Its proof removes the maximal-extension step from the parent: choose a graph with maximum edge count from the finite set of eligible simple graphs, then use strict inclusion to contradict maximality. A concrete independent Lean route is a finite maximization over the subtype of simple graphs containing G and satisfying the drawing predicate, using classical finiteness and strict cardinality growth under strict inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_edge_maximal_supergraph_for_triangulated_edge_count_bound_2eec570b_ffd5_435e_a8fa_d87718384d1c
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet ⊆ H.edgeSet := by sorry
