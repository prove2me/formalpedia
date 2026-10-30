-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_from_euler_face_data__p2m_610b0216_a272_4b4e_8618_1ead071ef542_a1
-- name    : WilliamsonShmoys.edge_bound_from_euler_face_data__p2m_610b0216_a272_4b4e_8618_1ead071ef542_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:36:58.094974+00:00
-- url     : https://prove2.me/theorems/e8556d1f-e6e5-4f67-90a9-b43d3a028c33
-- title:
--   Edge bound from Euler and face data
-- statement:
--   If a finite dart type has twice as many elements as there are edges, the vertex-face-edge counts satisfy Euler’s equation, and every face fiber has at least three darts, then the planar edge bound follows.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edge_bound_from_euler_face_data__p2m_610b0216_a272_4b4e_8618_1ead071ef542_a1
    (n q e : ℕ)
    (D : Type) [Fintype D]
    (face : D → Fin q)
    (hD : Fintype.card D = 2 * e)
    (hEuler : n + q = e + 2)
    (hFaces : ∀ f : Fin q,
      3 ≤ Fintype.card {d : D // face d = f}) :
    e + 6 ≤ 3 * n := by sorry
