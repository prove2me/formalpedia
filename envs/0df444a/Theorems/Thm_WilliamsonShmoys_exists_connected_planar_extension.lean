-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_connected_planar_extension
-- name    : WilliamsonShmoys.exists_connected_planar_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T13:23:37.418306+00:00
-- url     : https://prove2.me/theorems/507e8611-70ee-46cb-a474-e2db832a8f1e
-- title:
--   Connected planar extension of a finite drawing
-- statement:
--   Every planar drawing on a nonempty finite linearly ordered vertex type has a connected planar extension on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_connected_planar_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 0 < Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ S : SimpleGraph V,
      R.edgeSet ⊆ S.edgeSet ∧ S.Connected ∧
        WilliamsonShmoys.HasPlanarDrawingOn S := by sorry
