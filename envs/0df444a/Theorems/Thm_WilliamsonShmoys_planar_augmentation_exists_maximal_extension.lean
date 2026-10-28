-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_exists_maximal_extension
-- name    : WilliamsonShmoys.planar_augmentation_exists_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:10:41.486031+00:00
-- url     : https://prove2.me/theorems/4d54e359-f2f1-4ac3-ae4e-2499b5e6ae0d
-- title:
--   Extend a finite planar graph to an edge-maximal planar supergraph
-- statement:
--   Every finite planar graph on at least three vertices has a planar supergraph on the same vertex set that is maximal under edge inclusion; the original edge set is included, so its edge count cannot decrease.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_augmentation_exists_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      (∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet ⊆ K.edgeSet) := by sorry
