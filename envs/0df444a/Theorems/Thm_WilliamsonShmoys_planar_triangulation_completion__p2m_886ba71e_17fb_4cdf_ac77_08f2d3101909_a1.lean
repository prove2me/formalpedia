-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_886ba71e_17fb_4cdf_ac77_08f2d3101909_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_886ba71e_17fb_4cdf_ac77_08f2d3101909_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:39:27.266707+00:00
-- url     : https://prove2.me/theorems/a751ad37-41e6-4dc6-8ec5-fa27c83e40b5
-- title:
--   Planar drawing extends to a triangulation on the same vertices
-- statement:
--   Any finite planar graph with at least three vertices has a planar supergraph on the same vertex set whose edge count is three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_886ba71e_17fb_4cdf_ac77_08f2d3101909_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ G : SimpleGraph V,
      H ≤ G ∧
      WilliamsonShmoys.HasPlanarDrawingOn G ∧
      G.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
