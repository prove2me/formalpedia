-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_adds_missing_edge
-- name    : WilliamsonShmoys.planar_augmentation_adds_missing_edge
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T22:46:29.160083+00:00
-- url     : https://prove2.me/theorems/4cca54da-235e-453e-bdfd-4b69b9f5b143
-- title:
--   Join planar components by a missing edge
-- statement:
--   A disconnected graph with the specified planar drawing has a planar supergraph on the same vertices that contains at least one new edge. This isolates the geometric augmentation step from edge counting. A proof must use the finite embedded components to find a face in which a joining arc can be drawn, while respecting the drawing definition’s continuity, injectivity, endpoint, and nonintersection conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_augmentation_adds_missing_edge
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hdisc : ¬ M.Connected) :
    ∃ N : SimpleGraph V,
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∃ u v, N.Adj u v ∧ ¬ M.Adj u v := by sorry
