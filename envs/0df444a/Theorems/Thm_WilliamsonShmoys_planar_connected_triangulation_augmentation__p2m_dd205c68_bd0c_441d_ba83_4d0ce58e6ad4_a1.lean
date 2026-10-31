-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_triangulation_augmentation__p2m_dd205c68_bd0c_441d_ba83_4d0ce58e6ad4_a1
-- name    : WilliamsonShmoys.planar_connected_triangulation_augmentation__p2m_dd205c68_bd0c_441d_ba83_4d0ce58e6ad4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:10:57.955539+00:00
-- url     : https://prove2.me/theorems/0e5c0c9f-81d3-4964-a5b1-5841809db03d
-- title:
--   Complete a connected planar drawing to a triangulation
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing extends on the same vertex set to a crossing-free graph with exactly 3|V|−6 edges, containing all its original edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_triangulation_augmentation__p2m_dd205c68_bd0c_441d_ba83_4d0ce58e6ad4_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hConnected : K.Connected) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard ∧ H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
