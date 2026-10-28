-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation
-- name    : WilliamsonShmoys.planar_drawing_connected_augmentation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:07:53.561391+00:00
-- url     : https://prove2.me/theorems/65bcb047-f556-40b4-af83-be9390a0ef12
-- title:
--   Connected augmentation of a finite planar drawing
-- statement:
--   Any finite planar drawing on at least three vertices can be extended to a connected planar simple graph on the same vertices that contains the original edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      (∀ u v, L.Adj u v → H.Adj u v) ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      L.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
