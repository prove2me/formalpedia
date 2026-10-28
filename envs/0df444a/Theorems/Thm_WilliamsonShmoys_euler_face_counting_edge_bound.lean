-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_face_counting_edge_bound
-- name    : WilliamsonShmoys.euler_face_counting_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T11:47:19.256292+00:00
-- url     : https://prove2.me/theorems/69ec4e92-8679-4696-a976-92e1d95214e6
-- title:
--   Euler face-counting data imply the planar edge bound
-- statement:
--   Euler’s equation, the sum of face boundary lengths, and the minimum face length of three imply the edge bound by arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.euler_face_counting_edge_bound
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (hcert : ∃ (m : ℕ) (boundaryLength : Fin m → ℕ),
      Fintype.card V + m = K.edgeSet.ncard + 2 ∧
      (∑ f : Fin m, boundaryLength f) = 2 * K.edgeSet.ncard ∧
      ∀ f, 3 <= boundaryLength f) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  sorry
