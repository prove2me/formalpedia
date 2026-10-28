-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_augmentation_v3
-- name    : WilliamsonShmoys.planar_edge_count_augmentation_v3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T14:42:39.690441+00:00
-- url     : https://prove2.me/theorems/a3e63dcd-0c79-4158-90ac-b76a05de521f
-- title:
--   Connected augmentation for the planar edge bound
-- statement:
--   A graph on at least three vertices with the packaged crossing-free drawing has a connected supergraph on the same vertices, with a crossing-free drawing and at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_augmentation_v3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Connected ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
