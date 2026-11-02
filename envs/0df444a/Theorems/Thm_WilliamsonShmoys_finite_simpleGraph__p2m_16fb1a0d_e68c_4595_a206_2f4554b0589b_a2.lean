-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simpleGraph__p2m_16fb1a0d_e68c_4595_a206_2f4554b0589b_a2
-- name    : WilliamsonShmoys.finite_simpleGraph__p2m_16fb1a0d_e68c_4595_a206_2f4554b0589b_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:22:03.143092+00:00
-- url     : https://prove2.me/theorems/bc095f07-2285-4d60-8af7-6f9b7cc5b1df
-- title:
--   Finiteness of simple graphs on a finite vertex type
-- statement:
--   For a finite linearly ordered vertex type, the type of simple graphs on it is finite.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

open SimpleGraph

theorem WilliamsonShmoys.finite_simpleGraph__p2m_16fb1a0d_e68c_4595_a206_2f4554b0589b_a2
    {V : Type} [Fintype V] [LinearOrder V] : Finite (SimpleGraph V) := by sorry
