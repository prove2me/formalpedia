-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_ed9a163f_a427_4bb6_adf9_73a7e049aa03_a1
-- name    : WilliamsonShmoys_planar_triangulation_extension__p2m_ed9a163f_a427_4bb6_adf9_73a7e049aa03_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:25:18.448608+00:00
-- url     : https://prove2.me/theorems/2d00307b-e04d-4990-9e5d-cdabacc381df
-- title:
--   Triangulate a connected planar drawing
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing can be extended, without adding vertices, to a simple planar graph whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys_planar_triangulation_extension__p2m_ed9a163f_a427_4bb6_adf9_73a7e049aa03_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
