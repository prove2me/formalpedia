-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_length_certificate_implies_edge_bound__p2m_1fede0fd_ca75_4d2a_8cf1_d73a70c51443_a1
-- name    : WilliamsonShmoys.face_length_certificate_implies_edge_bound__p2m_1fede0fd_ca75_4d2a_8cf1_d73a70c51443_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T08:25:24.227795+00:00
-- url     : https://prove2.me/theorems/4ccc9d1c-62bb-40e2-9c3e-9ae040e3cacd
-- title:
--   Counting from face boundary lengths
-- statement:
--   If a finite list of face lengths satisfies Euler’s count, sums to twice the number of edges, and every listed length is at least three, then the number of edges is at most three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Data.List.Basic
set_option autoImplicit false

theorem WilliamsonShmoys.face_length_certificate_implies_edge_bound__p2m_1fede0fd_ca75_4d2a_8cf1_d73a70c51443_a1
    {n m : Nat} (faces : List Nat)
    (hN : 3 <= n)
    (hEuler : (n : Int) - (m : Int) + (faces.length : Int) = 2)
    (hSum : faces.sum = 2 * m)
    (hFace : ∀ length ∈ faces, 3 <= length) :
    (m : Int) <= 3 * (n : Int) - 6 := by sorry
