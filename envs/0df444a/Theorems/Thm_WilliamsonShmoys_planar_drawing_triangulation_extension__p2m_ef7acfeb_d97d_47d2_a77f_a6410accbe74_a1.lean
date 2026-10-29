-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_ef7acfeb_d97d_47d2_a77f_a6410accbe74_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_ef7acfeb_d97d_47d2_a77f_a6410accbe74_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T23:26:29.46185+00:00
-- url     : https://prove2.me/theorems/b76a54ef-1c48-4c54-85f5-81d888cceed1
-- title:
--   Triangulation extension for a finite planar drawing
-- statement:
--   Every finite simple graph on at least three vertices with the specified crossing-free drawing is contained in a graph on the same vertex set that also has such a drawing and has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_ef7acfeb_d97d_47d2_a77f_a6410accbe74_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  sorry
