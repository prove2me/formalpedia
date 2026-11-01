-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_c996decd_a3a2_408a_aa7c_25c4f85a8988_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_c996decd_a3a2_408a_aa7c_25c4f85a8988_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:36:55.696305+00:00
-- url     : https://prove2.me/theorems/9bfbc735-ec6d-4d27-8e0c-d58af3810de3
-- title:
--   Drawable planar triangulation extension has the exact edge count
-- statement:
--   For a finite linearly ordered vertex type with at least three vertices, any graph with a crossing-free drawing has a drawable supergraph on the same vertices whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_c996decd_a3a2_408a_aa7c_25c4f85a8988_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 = K.edgeSet.ncard := by sorry
