-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_triangulated
-- name    : WilliamsonShmoys.planar_drawing_augmentation_triangulated
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T04:35:06.403958+00:00
-- url     : https://prove2.me/theorems/49abde41-f0f9-4c3a-8f8a-eb1ea4493991
-- title:
--   Triangulated augmentation of a connected planar drawing
-- statement:
--   Every connected finite simple graph with at least three vertices and a crossing-free drawing can be augmented on the same vertex set to a crossing-free simple graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_augmentation_triangulated
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConnected : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (H.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
