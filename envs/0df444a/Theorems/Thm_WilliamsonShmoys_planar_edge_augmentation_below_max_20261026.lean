-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_below_max_20261026
-- name    : WilliamsonShmoys.planar_edge_augmentation_below_max_20261026
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T01:23:11.15014+00:00
-- url     : https://prove2.me/theorems/9ab8addf-f979-4a57-9295-60dc8b3e4e06
-- title:
--   Augmenting a nonmaximal planar graph
-- statement:
--   A graph with the supplied planar drawing and fewer than the maximal planar edge count has a proper planar supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_augmentation_below_max_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hSmall : K.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ J : SimpleGraph V,
      K ≤ J ∧ J ≠ K ∧ WilliamsonShmoys.HasPlanarDrawingOn J := by sorry
