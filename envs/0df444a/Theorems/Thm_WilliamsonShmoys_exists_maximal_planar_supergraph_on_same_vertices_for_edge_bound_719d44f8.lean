-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_on_same_vertices_for_edge_bound_719d44f8
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_on_same_vertices_for_edge_bound_719d44f8
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:45:31.59177+00:00
-- url     : https://prove2.me/theorems/9538c7a8-17aa-406f-ad1c-e0bdce92c761
-- title:
--   Extend a drawable graph to a maximal drawable supergraph
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices is contained in an edge-maximal drawable graph on the same vertices, with no fewer edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_on_same_vertices_for_edge_bound_719d44f8
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
