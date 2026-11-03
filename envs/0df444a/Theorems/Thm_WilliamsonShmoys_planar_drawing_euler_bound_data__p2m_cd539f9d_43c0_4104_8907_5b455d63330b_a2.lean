-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_bound_data__p2m_cd539f9d_43c0_4104_8907_5b455d63330b_a2
-- name    : WilliamsonShmoys.planar_drawing_euler_bound_data__p2m_cd539f9d_43c0_4104_8907_5b455d63330b_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:55:33.035978+00:00
-- url     : https://prove2.me/theorems/c26dc073-3bb3-419b-aef0-cb3d89286f37
-- title:
--   Euler data for a connected planar drawing
-- statement:
--   For a finite simple connected graph with at least three vertices and a crossing-free drawing, there is a face count satisfying Euler’s equation and the total face-degree bound. This child isolates the topological work needed by the target. A proof route is to construct the planar map induced by the drawing, apply Euler’s formula, then count edge sides in facial boundary walks; connectedness and the vertex lower bound rule out the small exceptional walks, while bridges are counted with both sides.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_bound_data__p2m_cd539f9d_43c0_4104_8907_5b455d63330b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     ∃ f : Nat,
       Fintype.card V + f = H.edgeFinset.card + 2 ∧
       3 * f ≤ 2 * H.edgeFinset.card) := by sorry
