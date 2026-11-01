-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_edge_bound__p2m_ed6487b5_3fd2_47fb_a969_c3848ac24208_a1
-- name    : WilliamsonShmoys.planar_connected_edge_bound__p2m_ed6487b5_3fd2_47fb_a969_c3848ac24208_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:39:44.395331+00:00
-- url     : https://prove2.me/theorems/c26a86c1-c11b-4f85-a158-b9e12bec4015
-- title:
--   Connected drawable graphs satisfy the planar edge bound
-- statement:
--   A finite connected simple graph with a crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_edge_bound__p2m_ed6487b5_3fd2_47fb_a969_c3848ac24208_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) (hcard : 3 <= Fintype.card V) :
    G.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  sorry
