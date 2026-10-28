-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_of_disconnected
-- name    : WilliamsonShmoys.planar_extension_of_disconnected
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T02:43:40.808657+00:00
-- url     : https://prove2.me/theorems/03b13259-8864-46c1-801c-a1a28189091d
-- title:
--   A disconnected planar graph has a planar proper edge extension
-- statement:
--   Every disconnected graph with a crossing-free drawing on a finite linearly ordered vertex type admits a crossing-free drawing after adding at least one edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_extension_of_disconnected
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : ¬ K.Connected) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      L.edgeSet ≠ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L := by
  sorry
