-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_certificate_edge_bound
-- name    : WilliamsonShmoys.euler_certificate_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:12:51.674827+00:00
-- url     : https://prove2.me/theorems/b5f506d8-5520-4c72-8620-1281d2bcf3f8
-- title:
--   Euler and incidence equations imply the planar edge bound
-- statement:
--   A natural face count satisfying Euler’s equation and triangular incidence gives the desired edge bound. Multiply the Euler equation by three, substitute the incidence equation, and simplify; this removes the numerical manipulation from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.euler_certificate_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (f : ℕ)
    (hEuler : Fintype.card V + f = K.edgeSet.ncard + 2)
    (hIncidence : 3 * f = 2 * K.edgeSet.ncard) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by sorry
