-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_count_from_drawing__p2m_c59fe07e_0bca_4d4e_9b09_8335007f2f58_a2
-- name    : WilliamsonShmoys_planar_face_count_from_drawing__p2m_c59fe07e_0bca_4d4e_9b09_8335007f2f58_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:43:17.237115+00:00
-- url     : https://prove2.me/theorems/78e6a567-9e35-4430-95ce-28355556e16a
-- title:
--   Euler and face counts from a connected planar drawing
-- statement:
--   For a connected finite simple graph with at least three vertices and the supplied crossing-free drawing, there is a natural-number face count satisfying Euler’s equation and the lower bound on total face-boundary length.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys_planar_face_count_from_drawing__p2m_c59fe07e_0bca_4d4e_9b09_8335007f2f58_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ f : ℕ,
      (Fintype.card V : ℤ) - (K.edgeSet.ncard : ℤ) + (f : ℤ) = 2 ∧
      (3 : ℤ) * (f : ℤ) ≤ 2 * (K.edgeSet.ncard : ℤ) := by sorry
