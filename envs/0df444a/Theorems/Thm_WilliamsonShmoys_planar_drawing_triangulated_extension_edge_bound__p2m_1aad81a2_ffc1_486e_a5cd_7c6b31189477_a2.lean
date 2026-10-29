-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_extension_edge_bound__p2m_1aad81a2_ffc1_486e_a5cd_7c6b31189477_a2
-- name    : WilliamsonShmoys.planar_drawing_triangulated_extension_edge_bound__p2m_1aad81a2_ffc1_486e_a5cd_7c6b31189477_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T21:13:29.095483+00:00
-- url     : https://prove2.me/theorems/bb4dce47-9275-45c5-899b-6355cecbb075
-- title:
--   Triangulated extension of a planar drawing
-- statement:
--   Any finite connected simple graph with at least three vertices and a crossing-free drawing on the plane’s point set can be extended, on the same vertex set, to a connected drawn graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulated_extension_edge_bound__p2m_1aad81a2_ffc1_486e_a5cd_7c6b31189477_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
