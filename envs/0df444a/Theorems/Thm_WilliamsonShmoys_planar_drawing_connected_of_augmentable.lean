-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_of_augmentable
-- name    : WilliamsonShmoys.planar_drawing_connected_of_augmentable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:17:31.257001+00:00
-- url     : https://prove2.me/theorems/08836067-3d90-44fd-8039-9c3392896c07
-- title:
--   Connected planar supergraph from strict augmentation
-- statement:
--   If every disconnected planar graph on a fixed finite vertex type has a strictly larger planar supergraph, then any given planar graph on that type has a connected planar supergraph containing it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_of_augmentable
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hAugment :
      ∀ X : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn X →
        ¬ X.Connected →
        ∃ Z : SimpleGraph V,
          X ≤ Z ∧
          X.edgeSet.ncard < Z.edgeSet.ncard ∧
          WilliamsonShmoys.HasPlanarDrawingOn Z) :
    ∃ Z : SimpleGraph V,
      Y ≤ Z ∧
      Y.edgeSet.ncard ≤ Z.edgeSet.ncard ∧
      Z.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn Z := by sorry
