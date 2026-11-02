-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_type__p2m_0d7f4e6a_f018_419b_9ff8_3c6696d14d6d_a1
-- name    : WilliamsonShmoys.finite_simpleGraph_type__p2m_0d7f4e6a_f018_419b_9ff8_3c6696d14d6d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:54:11.435247+00:00
-- url     : https://prove2.me/theorems/cd70b53c-5d17-4ac5-ad3b-ec3e9f008ab7
-- title:
--   Finiteness of simple graphs on a finite vertex type
-- statement:
--   For a finite vertex type, the type of simple graphs on that vertex type is finite.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

open SimpleGraph

theorem WilliamsonShmoys.finite_simpleGraph_type__p2m_0d7f4e6a_f018_419b_9ff8_3c6696d14d6d_a1 {V : Type} [Fintype V] : Finite (SimpleGraph V) := by sorry
