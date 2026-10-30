-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_augmentation
-- name    : WilliamsonShmoys.planar_drawing_triangulation_augmentation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:16:14.789043+00:00
-- url     : https://prove2.me/theorems/d1503eb1-0fde-451f-95cc-9e34d85d2bae
-- title:
--   Augment a planar drawing to a triangulation
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges. This isolates the planar augmentation and triangulation argument without assuming maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hV : 3 ≤ Fintype.card V) :
    ∃ X : SimpleGraph V, W ≤ X ∧ WilliamsonShmoys.HasPlanarDrawingOn X ∧
      3 * Fintype.card V = X.edgeSet.ncard + 6 := by sorry
