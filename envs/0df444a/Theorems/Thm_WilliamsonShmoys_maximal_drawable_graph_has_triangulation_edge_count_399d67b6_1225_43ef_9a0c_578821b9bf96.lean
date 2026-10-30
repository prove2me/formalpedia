-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulation_edge_count_399d67b6_1225_43ef_9a0c_578821b9bf96
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count_399d67b6_1225_43ef_9a0c_578821b9bf96
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:30:57.088367+00:00
-- url     : https://prove2.me/theorems/bd88397e-ac56-4c39-ba2b-ef0c758c40a5
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable finite simple graph on at least three vertices that is maximal among drawable supergraphs has exactly 3|V|−6 edges. The drawing is a plane embedding; maximality implies connectedness and triangular faces, including the three-vertex boundary case. Euler’s formula and face-edge incidence counting then give the exact edge count. This isolates the topological core from the finite maximal-extension argument. The remaining proof work is formalizing the embedding, face-boundary, and Euler arguments for the supplied arc-based drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count_399d67b6_1225_43ef_9a0c_578821b9bf96
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet ⊆ L.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
