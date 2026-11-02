-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_equation_data__p2m_c26dc073_3bb3_419b_aef0_cb3d89286f37_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_equation_data__p2m_c26dc073_3bb3_419b_aef0_cb3d89286f37_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:08:22.47157+00:00
-- url     : https://prove2.me/theorems/7f4c1ad2-4413-457d-ae8f-8936a6ba8a01
-- title:
--   Euler equation for a connected planar drawing
-- statement:
--   A finite connected graph with a crossing-free drawing has a natural-number face count satisfying Euler’s equation. The independent proof route is to form the planar map from the drawing, use connectedness to apply Euler’s formula, and identify the map’s vertices and edges with those of the graph. This isolates the Euler/map construction; it does not establish the planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_equation_data__p2m_c26dc073_3bb3_419b_aef0_cb3d89286f37_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     ∃ f : Nat,
       Fintype.card V + f = H.edgeFinset.card + 2) := by sorry
