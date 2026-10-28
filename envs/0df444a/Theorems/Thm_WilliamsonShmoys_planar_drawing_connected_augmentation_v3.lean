-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_v3
-- name    : WilliamsonShmoys.planar_drawing_connected_augmentation_v3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T10:16:01.035996+00:00
-- url     : https://prove2.me/theorems/fe6d83cd-9135-4f00-96cb-86d37ec4672e
-- title:
--   Connect a planar drawing while preserving its edges
-- statement:
--   Given a finite drawn graph on at least three vertices, extend it on the same vertex type to a connected graph with a planar drawing, preserving all original edges and not decreasing the edge count. The size hypothesis rules out the empty-vertex counterexample to the earlier augmentation statement.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_connected_augmentation_v3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun H : SimpleGraph V =>
      (forall u v : V, K.Adj u v -> H.Adj u v) /\
      K.edgeSet.ncard <= H.edgeSet.ncard /\
      H.Connected /\
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  sorry
