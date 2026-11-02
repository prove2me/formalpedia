-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph__p2m_4d9d61b3_a3d4_4adb_a77f_fb6a2cb8e8dc_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_4d9d61b3_a3d4_4adb_a77f_fb6a2cb8e8dc_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T07:48:28.873204+00:00
-- url     : https://prove2.me/theorems/b6f7b032-7d17-4abc-a25e-6614208f3ad2
-- title:
--   Connected planar supergraph on the same vertices
-- statement:
--   Every finite graph with a crossing-free drawing has a connected planar supergraph on the same vertices. The construction preserves all existing edges and connects the drawing's components through the complement; isolated vertices are included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_4d9d61b3_a3d4_4adb_a77f_fb6a2cb8e8dc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
