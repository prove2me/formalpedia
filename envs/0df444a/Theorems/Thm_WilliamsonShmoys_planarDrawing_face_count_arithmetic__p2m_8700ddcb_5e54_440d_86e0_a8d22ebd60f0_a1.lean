-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_face_count_arithmetic__p2m_8700ddcb_5e54_440d_86e0_a8d22ebd60f0_a1
-- name    : WilliamsonShmoys.planarDrawing_face_count_arithmetic__p2m_8700ddcb_5e54_440d_86e0_a8d22ebd60f0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:35:26.681558+00:00
-- url     : https://prove2.me/theorems/88616743-91e7-440f-904d-e5292bfb9687
-- title:
--   Arithmetic consequence of planar face counts
-- statement:
--   Given Euler's relation for vertex, face, and edge counts, a face-length sum of twice the edge count, and length at least three for each face, the edge count satisfies the planar bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawing_face_count_arithmetic__p2m_8700ddcb_5e54_440d_86e0_a8d22ebd60f0_a1
    (n f e : Nat) (faceLength : Fin f → Nat)
    (hEuler : n + f = e + 2)
    (hTotalLength : (∑ i : Fin f, faceLength i) = 2 * e)
    (hFaceLength : ∀ i : Fin f, 3 ≤ faceLength i) :
    e + 6 ≤ 3 * n := by sorry
