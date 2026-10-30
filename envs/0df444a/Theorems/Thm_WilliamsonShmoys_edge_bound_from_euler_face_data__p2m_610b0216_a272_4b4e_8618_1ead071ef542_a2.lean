-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_from_euler_face_data__p2m_610b0216_a272_4b4e_8618_1ead071ef542_a2
-- name    : WilliamsonShmoys.edge_bound_from_euler_face_data__p2m_610b0216_a272_4b4e_8618_1ead071ef542_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:42:28.125538+00:00
-- url     : https://prove2.me/theorems/0810a96b-16b7-4127-8947-096014b5055d
-- title:
--   Edge bound from Euler and face data
-- statement:
--   Given a finite dart type with twice the edge count, Euler’s vertex-face-edge equation, and at least three darts in every face fiber, the number of edges plus six is at most three times the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edge_bound_from_euler_face_data__p2m_610b0216_a272_4b4e_8618_1ead071ef542_a2
    (n q e : ℕ)
    (D : Type) [Fintype D]
    (face : D → Fin q)
    (hD : Fintype.card D = 2 * e)
    (hEuler : n + q = e + 2)
    (hFaces : ∀ f : Fin q,
      3 ≤ Fintype.card {d : D // face d = f}) :
    e + 6 ≤ 3 * n := by sorry
