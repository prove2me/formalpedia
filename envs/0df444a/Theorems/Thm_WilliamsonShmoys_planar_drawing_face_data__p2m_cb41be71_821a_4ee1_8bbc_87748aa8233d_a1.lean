-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_data__p2m_cb41be71_821a_4ee1_8bbc_87748aa8233d_a1
-- name    : WilliamsonShmoys.planar_drawing_face_data__p2m_cb41be71_821a_4ee1_8bbc_87748aa8233d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:02:29.121752+00:00
-- url     : https://prove2.me/theorems/dbfda827-a827-4911-8354-de916f36b6c0
-- title:
--   Euler and face-boundary count for a simple planar drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and the supplied crossing-free drawing, there is a natural number f satisfying Euler’s vertex-edge-face equation and the total face-boundary lower bound, expressed as 3f ≤ 2E.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_data__p2m_cb41be71_821a_4ee1_8bbc_87748aa8233d_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (dK : DecidableRel K.Adj) (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hcard : 3 <= Fintype.card V) : ∃ f : ℕ, Fintype.card V + f = K.edgeFinset.card + 2 ∧ 3 * f <= 2 * K.edgeFinset.card := by sorry
