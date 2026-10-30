-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_for_maximal_drawable
-- name    : WilliamsonShmoys.planar_edge_augmentation_for_maximal_drawable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T11:42:17.227886+00:00
-- url     : https://prove2.me/theorems/67a4185f-2b93-4ba7-a497-3dfa7054de8c
-- title:
--   Augmentation below the planar edge bound
-- statement:
--   Any drawable simple graph on at least three finite vertices with fewer than 3|V|−6 edges has a strict drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_augmentation_for_maximal_drawable
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hV : 3 ≤ Fintype.card V)
    (hgap : T.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ U : SimpleGraph V,
      T ≤ U ∧ U ≠ T ∧ WilliamsonShmoys.HasPlanarDrawingOn U := by sorry
