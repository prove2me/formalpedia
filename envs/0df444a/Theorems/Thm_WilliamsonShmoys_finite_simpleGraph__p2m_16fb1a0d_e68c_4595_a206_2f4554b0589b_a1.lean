-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simpleGraph__p2m_16fb1a0d_e68c_4595_a206_2f4554b0589b_a1
-- name    : WilliamsonShmoys.finite_simpleGraph__p2m_16fb1a0d_e68c_4595_a206_2f4554b0589b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:01:02.567229+00:00
-- url     : https://prove2.me/theorems/ff811ce2-ce8d-4a73-9c63-cb820da1c91a
-- title:
--   Finiteness of simple graphs on a finite vertex type
-- statement:
--   For a finite linearly ordered vertex type, the type of simple graphs on it is finite.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

open SimpleGraph

theorem WilliamsonShmoys.finite_simpleGraph__p2m_16fb1a0d_e68c_4595_a206_2f4554b0589b_a1
    {V : Type} [Fintype V] [LinearOrder V] : Finite (SimpleGraph V) := by sorry
