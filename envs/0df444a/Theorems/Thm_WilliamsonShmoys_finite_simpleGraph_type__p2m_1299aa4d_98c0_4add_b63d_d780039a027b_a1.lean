-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_type__p2m_1299aa4d_98c0_4add_b63d_d780039a027b_a1
-- name    : WilliamsonShmoys.finite_simpleGraph_type__p2m_1299aa4d_98c0_4add_b63d_d780039a027b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:42:54.754418+00:00
-- url     : https://prove2.me/theorems/f15bf77e-5f6d-4a55-a4ef-4ce09855e7ed
-- title:
--   Finiteness of simple graphs on a finite type
-- statement:
--   The type of simple graphs on a finite vertex type is finite.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.finite_simpleGraph_type__p2m_1299aa4d_98c0_4add_b63d_d780039a027b_a1 {V : Type} [Fintype V] : Finite (SimpleGraph V) := by sorry
