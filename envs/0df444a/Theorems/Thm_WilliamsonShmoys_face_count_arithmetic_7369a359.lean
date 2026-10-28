-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_count_arithmetic_7369a359
-- name    : WilliamsonShmoys.face_count_arithmetic_7369a359
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T11:43:42.638078+00:00
-- url     : https://prove2.me/theorems/7adb3518-aa7c-40a2-b4df-9c93523f9d8b
-- title:
--   Recovering the face count from the maximal planar edge count
-- statement:
--   For natural numbers n ≥ 3 and e = 3n−6, the value f = 2n−4 satisfies the two requested equations. This isolates the parent’s final arithmetic from its planar-graph argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.face_count_arithmetic_7369a359
    (n e : Nat)
    (hCard : 3 <= n)
    (hEdges : e + 6 = 3 * n) :
    exists f : Nat,
      n + f = e + 2 /\
      3 * f = 2 * e := by sorry
