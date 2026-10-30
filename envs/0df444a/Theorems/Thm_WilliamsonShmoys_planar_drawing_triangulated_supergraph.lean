-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_supergraph
-- name    : WilliamsonShmoys.planar_drawing_triangulated_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:08:39.385785+00:00
-- url     : https://prove2.me/theorems/543ac5d4-f428-40a1-b27b-e0d421d46a32
-- title:
--   Triangulated supergraph of a planar drawing
-- statement:
--   Every finite simple graph with at least three vertices that has a crossing-free drawing can be extended, using only its existing vertices, to a drawable triangulated graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulated_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S) :
    ∃ T : SimpleGraph V,
      S <= T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
        3 * Fintype.card V = T.edgeSet.ncard + 6 := by sorry
