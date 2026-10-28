-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_to_triangulation
-- name    : WilliamsonShmoys.planar_drawing_augmentation_to_triangulation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:31:12.593967+00:00
-- url     : https://prove2.me/theorems/136dc8a1-c6f7-458f-b5aa-0bd702303ad4
-- title:
--   Augment a planar drawing to a triangulation
-- statement:
--   Every graph on a finite linearly ordered vertex type with at least three vertices that has a crossing-free arc drawing is a subgraph of a graph on the same vertex set that also has such a drawing and has exactly three times the vertex count minus six edges. The order and vertex count hypotheses are retained because the drawing predicate uses the order and the edge formula requires at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_augmentation_to_triangulation
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
