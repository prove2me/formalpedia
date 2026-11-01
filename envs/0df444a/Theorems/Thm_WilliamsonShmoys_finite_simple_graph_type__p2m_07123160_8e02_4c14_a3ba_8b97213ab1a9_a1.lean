-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simple_graph_type__p2m_07123160_8e02_4c14_a3ba_8b97213ab1a9_a1
-- name    : WilliamsonShmoys.finite_simple_graph_type__p2m_07123160_8e02_4c14_a3ba_8b97213ab1a9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:25:25.172805+00:00
-- url     : https://prove2.me/theorems/40404a47-1d98-464c-b6f0-46be95374e0f
-- title:
--   Simple graphs on a finite type form a finite type
-- statement:
--   For a finite vertex type, there are only finitely many simple graphs on that type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_simple_graph_type__p2m_07123160_8e02_4c14_a3ba_8b97213ab1a9_a1 {V : Type} [Fintype V] : Finite (SimpleGraph V) := by sorry
