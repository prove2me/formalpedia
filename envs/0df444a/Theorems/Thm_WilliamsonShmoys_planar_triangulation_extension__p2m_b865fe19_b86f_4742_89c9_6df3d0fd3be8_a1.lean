-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_b865fe19_b86f_4742_89c9_6df3d0fd3be8_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_b865fe19_b86f_4742_89c9_6df3d0fd3be8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:21:27.375403+00:00
-- url     : https://prove2.me/theorems/b5de7163-4173-4d75-853e-5e2f32ae30ae
-- title:
--   Same-vertex triangulation extension and edge count
-- statement:
--   Every graph with the given crossing-free drawing on at least three vertices is a subgraph of a triangulated simple planar graph on the same vertex set, whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_b865fe19_b86f_4742_89c9_6df3d0fd3be8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
