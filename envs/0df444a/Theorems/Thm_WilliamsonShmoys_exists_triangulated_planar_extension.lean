-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_extension
-- name    : WilliamsonShmoys.exists_triangulated_planar_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T13:23:59.583333+00:00
-- url     : https://prove2.me/theorems/393393b3-28c4-4b78-a49c-41fa02172373
-- title:
--   Maximally edged extension of a connected planar drawing
-- statement:
--   A connected planar drawing on at least three vertices extends, on the same vertices, to a planar graph with exactly `3n - 6` edges. A proof route is to triangulate the faces of the connected embedding and apply Euler's formula; the equality records the resulting edge count and supplies the extension property needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_triangulated_planar_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hConn : R.Connected)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ S : SimpleGraph V,
      R.edgeSet ⊆ S.edgeSet ∧
        WilliamsonShmoys.HasPlanarDrawingOn S ∧
        S.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
