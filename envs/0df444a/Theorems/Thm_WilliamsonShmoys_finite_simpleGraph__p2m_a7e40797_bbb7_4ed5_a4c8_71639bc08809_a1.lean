-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simpleGraph__p2m_a7e40797_bbb7_4ed5_a4c8_71639bc08809_a1
-- name    : WilliamsonShmoys.finite_simpleGraph__p2m_a7e40797_bbb7_4ed5_a4c8_71639bc08809_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:48:24.241131+00:00
-- url     : https://prove2.me/theorems/49e8b471-2771-4342-bcb4-7e6ac4625dca
-- title:
--   Finiteness of simple graphs on a finite vertex type
-- statement:
--   The type of simple graphs on a finite vertex type is finite.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_simpleGraph__p2m_a7e40797_bbb7_4ed5_a4c8_71639bc08809_a1
    {V : Type} [Fintype V] : Finite (SimpleGraph V) := by sorry
