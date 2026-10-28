-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_strict_edge_augmentation
-- name    : WilliamsonShmoys.planar_drawing_strict_edge_augmentation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T17:54:28.680797+00:00
-- url     : https://prove2.me/theorems/d3f6855c-e788-4eb5-b9d7-df4909b92559
-- title:
--   Augmenting a planar drawing with a strict edge deficit
-- statement:
--   If a finite simple graph with a crossing-free drawing on at least three vertices has fewer than 3|V|−6 edges, it has a drawable proper supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_strict_edge_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hStrict : K.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    exists L : SimpleGraph V,
      K <= L /\ (L = K -> False) /\
        WilliamsonShmoys.HasPlanarDrawingOn L := by
  sorry
