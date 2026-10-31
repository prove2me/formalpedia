-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_of_finite_vertices__p2m_a874f652_e0a4_4d47_9ec5_8884fbe44a1d_a2
-- name    : WilliamsonShmoys.finite_simpleGraph_of_finite_vertices__p2m_a874f652_e0a4_4d47_9ec5_8884fbe44a1d_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:55:40.945986+00:00
-- url     : https://prove2.me/theorems/6ccfc5d7-c4c6-4745-998e-f4ff6d7b675f
-- title:
--   Finitely many simple graphs on a finite vertex type
-- statement:
--   The type of simple graphs on a finite vertex type is finite.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_simpleGraph_of_finite_vertices__p2m_a874f652_e0a4_4d47_9ec5_8884fbe44a1d_a2 {V : Type} [Finite V] : Finite (SimpleGraph V) := by sorry
