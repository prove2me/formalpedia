-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_simple_edge_bound__p2m_62a3a1a3_c41c_45ae_9d73_85a6165d1dd4_a1
-- name    : WilliamsonShmoys.planar_drawing_simple_edge_bound__p2m_62a3a1a3_c41c_45ae_9d73_85a6165d1dd4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:21:24.885465+00:00
-- url     : https://prove2.me/theorems/7318f0dd-6f83-40ec-a6c0-abefe8861b38
-- title:
--   Simple planar edge bound
-- statement:
--   A connected simple planar graph with at least three vertices has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_simple_edge_bound__p2m_62a3a1a3_c41c_45ae_9d73_85a6165d1dd4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
