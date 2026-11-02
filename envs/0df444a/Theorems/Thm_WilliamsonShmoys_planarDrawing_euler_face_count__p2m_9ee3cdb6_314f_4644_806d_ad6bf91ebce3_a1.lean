-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_euler_face_count__p2m_9ee3cdb6_314f_4644_806d_ad6bf91ebce3_a1
-- name    : WilliamsonShmoys.planarDrawing_euler_face_count__p2m_9ee3cdb6_314f_4644_806d_ad6bf91ebce3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:40:29.079685+00:00
-- url     : https://prove2.me/theorems/bab0c4ec-c654-47fe-97f8-5f2582f1ac75
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A connected graph with at least three vertices and a crossing-free drawing has a positive number of faces satisfying Euler’s vertex-edge-face equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_euler_face_count__p2m_9ee3cdb6_314f_4644_806d_ad6bf91ebce3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : Nat, 0 < f ∧
      Fintype.card V + f =
        (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 2 := by sorry
