-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_data__p2m_30c809bc_d869_43a8_8404_fcf85ec28b0f_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_face_data__p2m_30c809bc_d869_43a8_8404_fcf85ec28b0f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:48:18.541768+00:00
-- url     : https://prove2.me/theorems/2135cd12-067c-4c2b-897d-63c20477eb0d
-- title:
--   Euler equation and face incidence for a connected planar drawing
-- statement:
--   A connected simple graph on at least three vertices with the supplied crossing-free arc drawing has an integer face count satisfying Euler’s equation, and three times that count is at most twice the number of edges. The Euler equation comes from the induced plane embedding; the inequality counts edge sides around facial walks, whose lengths are at least three. For trees, the single face boundary walk traverses bridges twice, and the condition of at least three vertices prevents a length-two exception.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_face_data__p2m_30c809bc_d869_43a8_8404_fcf85ec28b0f_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hconn : T.Connected) : ∃ f : ℤ, (Fintype.card V : ℤ) - (T.edgeSet.ncard : ℤ) + f = 2 ∧ 3 * f ≤ 2 * (T.edgeSet.ncard : ℤ) := by sorry
