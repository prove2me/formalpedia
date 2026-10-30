-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_walk_counting_bound__p2m_1aa142c3_2879_49d1_9ded_02a2d2269a9c_a2
-- name    : WilliamsonShmoys.face_walk_counting_bound__p2m_1aa142c3_2879_49d1_9ded_02a2d2269a9c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T09:33:41.748728+00:00
-- url     : https://prove2.me/theorems/a29276fb-b540-46d8-a047-ddd967481e1e
-- title:
--   Counting facial boundary walks gives the edge bound
-- statement:
--   If facial lengths obey the Euler count, sum to twice the edge count, and are each at least three, then the edge count is at most three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Data.List.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.face_walk_counting_bound__p2m_1aa142c3_2879_49d1_9ded_02a2d2269a9c_a2
    (e v : ℕ)
    (faceLengths : List ℕ)
    (hEuler : faceLengths.length = e - v + 2)
    (hSum : faceLengths.sum = 2 * e)
    (hFace : ∀ ℓ ∈ faceLengths, 3 ≤ ℓ) :
    e + 6 ≤ 3 * v := by sorry
