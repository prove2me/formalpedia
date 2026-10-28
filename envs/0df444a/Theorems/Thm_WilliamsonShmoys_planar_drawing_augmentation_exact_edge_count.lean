-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_exact_edge_count
-- name    : WilliamsonShmoys.planar_drawing_augmentation_exact_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T04:08:15.820881+00:00
-- url     : https://prove2.me/theorems/27ebe3c7-de05-4ecd-b2e0-015385be129a
-- title:
--   Planar augmentation to the sharp edge count
-- statement:
--   Any finite simple graph with at least three vertices and a planar drawing has a planar supergraph on the same vertex type with exactly 3|V|−6 edges. The boundary case of three vertices gives the triangle. This constructive extension statement has no maximality hypothesis and supplies the specific supergraph needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_augmentation_exact_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hV : 3 <= Fintype.card V) :
    ∃ U : SimpleGraph V,
      T ≤ U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      U.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
