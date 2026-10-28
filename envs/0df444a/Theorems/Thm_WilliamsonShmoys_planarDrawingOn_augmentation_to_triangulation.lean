-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_augmentation_to_triangulation
-- name    : WilliamsonShmoys.planarDrawingOn_augmentation_to_triangulation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T17:00:22.374277+00:00
-- url     : https://prove2.me/theorems/fe74ac1b-216e-4ca8-b058-0b3c4a531007
-- title:
--   Augment a planar drawing to a triangulation
-- statement:
--   Any finite graph with at least three vertices and a crossing-free drawing has a planar supergraph on the same vertex set with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planarDrawingOn_augmentation_to_triangulation
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
