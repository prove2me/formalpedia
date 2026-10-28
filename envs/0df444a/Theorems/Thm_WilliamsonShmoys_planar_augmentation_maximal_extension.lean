-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_maximal_extension
-- name    : WilliamsonShmoys.planar_augmentation_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:36:28.939792+00:00
-- url     : https://prove2.me/theorems/9d1be5cd-13cf-45b3-bf34-79039cf4737b
-- title:
--   Finite maximal drawable supergraph extension
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph maximal under edge inclusion among drawable supergraphs on that same type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_augmentation_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ X : SimpleGraph V, W.edgeSet ⊆ X.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn X ∧
      ∀ Y : SimpleGraph V, X.edgeSet ⊆ Y.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn Y → Y.edgeSet ⊆ X.edgeSet := by sorry
