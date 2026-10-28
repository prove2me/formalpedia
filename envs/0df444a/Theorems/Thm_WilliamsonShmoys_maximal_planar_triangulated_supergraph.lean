-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulated_supergraph
-- name    : WilliamsonShmoys.maximal_planar_triangulated_supergraph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T13:07:30.095058+00:00
-- url     : https://prove2.me/theorems/ac1a1c00-b7f0-45aa-82c1-64875af5decb
-- title:
--   Every planar drawing extends to a triangulated planar supergraph
-- statement:
--   For any finite ordered vertex type with at least three vertices, every graph with a drawing satisfying HasPlanarDrawingOn has a planar supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_triangulated_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H <= K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
