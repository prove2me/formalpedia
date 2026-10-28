-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_lower_bound
-- name    : WilliamsonShmoys.planar_drawing_augmentation_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:53:48.800555+00:00
-- url     : https://prove2.me/theorems/dfe71645-fdc0-4fca-9b99-b202026249e9
-- title:
--   Drawable supergraphs reach the planar edge lower bound
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with at least 3|V|−6 edges. A classical proof augments the drawing to a triangulated planar graph and applies Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_augmentation_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V,
      J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        3 * Fintype.card V <= K.edgeSet.ncard + 6 := by sorry
