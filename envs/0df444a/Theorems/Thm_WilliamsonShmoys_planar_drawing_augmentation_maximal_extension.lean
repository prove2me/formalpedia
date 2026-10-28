-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_maximal_extension
-- name    : WilliamsonShmoys.planar_drawing_augmentation_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:11:09.097235+00:00
-- url     : https://prove2.me/theorems/cf45c473-7201-472a-bb1f-85d616c3bf19
-- title:
--   A drawable graph has a maximum-edge drawable extension
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph whose edge count is at least that of every drawable supergraph of it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_augmentation_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V,
      J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L →
          L.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
