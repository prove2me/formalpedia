-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_one_step_extension__p2m_e072abf9_a18d_4ec4_b40d_84b33bde54a7_a1
-- name    : WilliamsonShmoys.planar_drawing_one_step_extension__p2m_e072abf9_a18d_4ec4_b40d_84b33bde54a7_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:01:27.741346+00:00
-- url     : https://prove2.me/theorems/4073f4d5-ff76-4438-9b90-1c257ec3d306
-- title:
--   Add a planar edge between disconnected vertices
-- statement:
--   For a finite linearly ordered vertex type, if a graph has a planar drawing and two vertices are in different connected components, there is a planar supergraph on the same vertices that retains every old edge and adds an edge between those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_one_step_extension__p2m_e072abf9_a18d_4ec4_b40d_84b33bde54a7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (u v : V)
    (hsep : ¬ G.Reachable u v) :
    ∃ K : SimpleGraph V,
      HasPlanarDrawingOn K ∧ G ≤ K ∧ K.Adj u v := by sorry
