-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_6294dfb9_01c6_44e4_b6a8_a896c7d41add_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_face_count__p2m_6294dfb9_01c6_44e4_b6a8_a896c7d41add_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:19:59.251013+00:00
-- url     : https://prove2.me/theorems/d2cac20f-0eaa-41e0-9de6-314a384b119f
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   For a connected finite simple graph with a crossing-free drawing, there is a natural-number face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_face_count__p2m_6294dfb9_01c6_44e4_b6a8_a896c7d41add_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hConnected : J.Connected) :
    ∃ f : ℕ, Fintype.card V + f = J.edgeSet.ncard + 2 := by sorry
