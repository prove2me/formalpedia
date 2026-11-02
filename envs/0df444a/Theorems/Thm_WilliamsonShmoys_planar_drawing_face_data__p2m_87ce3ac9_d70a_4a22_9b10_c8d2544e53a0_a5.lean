-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_data__p2m_87ce3ac9_d70a_4a22_9b10_c8d2544e53a0_a5
-- name    : WilliamsonShmoys.planar_drawing_face_data__p2m_87ce3ac9_d70a_4a22_9b10_c8d2544e53a0_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:03:13.002201+00:00
-- url     : https://prove2.me/theorems/8200ad1b-21ab-4940-b689-6436a234b071
-- title:
--   Extract finite face data from a planar drawing
-- statement:
--   A connected simple graph on at least three vertices with the given crossing-free drawing has a finite list of faces whose boundary lengths are at least three, sum to twice the number of edges, and satisfy Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_face_data__p2m_87ce3ac9_d70a_4a22_9b10_c8d2544e53a0_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (m : ℕ) (faceLength : Fin m → ℕ),
      (∀ f, 3 ≤ faceLength f) ∧
      (∑ f : Fin m, faceLength f = 2 * H.edgeFinset.card) ∧
      (Fintype.card V + m = H.edgeFinset.card + 2) := by
  sorry
