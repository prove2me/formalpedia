-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connectivity_augmentation_c3c27980_9f1d_4b26_ac26_4100a7115914
-- name    : WilliamsonShmoys.planar_connectivity_augmentation_c3c27980_9f1d_4b26_ac26_4100a7115914
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T04:34:57.301334+00:00
-- url     : https://prove2.me/theorems/b05e6465-0cdb-4865-a3ab-a414d06d9de9
-- title:
--   Connect a planar graph by adding edges
-- statement:
--   A graph with the given crossing-free drawing has a connected planar supergraph on the same vertex type, with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connectivity_augmentation_c3c27980_9f1d_4b26_ac26_4100a7115914
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ S : SimpleGraph V,
      R.edgeSet.ncard ≤ S.edgeSet.ncard ∧
      S.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn S := by
  sorry
