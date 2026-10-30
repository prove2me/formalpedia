-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_degree_sum__p2m_7cf11437_ccf4_4d59_ac0e_83c393976ef1_a1
-- name    : WilliamsonShmoys.planar_drawing_face_degree_sum__p2m_7cf11437_ccf4_4d59_ac0e_83c393976ef1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:15:21.689076+00:00
-- url     : https://prove2.me/theorems/8cec4366-35b2-432d-b040-b53e5778430a
-- title:
--   Face-degree bound for a connected planar drawing
-- statement:
--   For any face count satisfying Euler’s formula for this drawing, the sum of face degrees is twice the number of edges and every face has degree at least three, so three times the face count is at most twice the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_degree_sum__p2m_7cf11437_ccf4_4d59_ac0e_83c393976ef1_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hconn : T.Connected) (f : ℕ) (hEuler : Fintype.card V + f = T.edgeSet.ncard + 2) : 3 * f ≤ 2 * T.edgeSet.ncard := by sorry
