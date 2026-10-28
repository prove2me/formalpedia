-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound_triangulation_extension
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_bound_triangulation_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T06:50:00.762391+00:00
-- url     : https://prove2.me/theorems/9ec54007-7901-4c23-ae78-4e059843aa72
-- title:
--   Triangulated drawable extension on a fixed vertex set
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_bound_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ Z : SimpleGraph V, W ≤ Z ∧ WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      3 * Fintype.card V = Z.edgeSet.ncard + 6 := by sorry
