-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_c00979a8
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph_c00979a8
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-27T00:24:48.968389+00:00
-- url     : https://prove2.me/theorems/9fdb82b1-e8fa-4a5c-9d04-cd703a1ed62e
-- title:
--   Connect components of this planar drawing
-- statement:
--   Extend a finite graph with the specified crossing-free drawing to a connected supergraph on the same vertices, preserving a drawing and not decreasing its edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_connected_supergraph_c00979a8 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
