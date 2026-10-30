-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_95ea5390
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_drawing_95ea5390
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T17:37:42.744343+00:00
-- url     : https://prove2.me/theorems/50797d53-bf24-4f33-8dfa-642a5d46806a
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   A finite drawable graph with at least three vertices that has no proper drawable supergraph on the same vertex type has exactly 3n−6 edges. For n=3 maximality forces the triangle; for larger n, the topological argument establishes a connected triangulation and applies Euler’s formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_maximal_planar_drawing_95ea5390
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
