-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_type_finite__p2m_cef71128_5f51_4c32_b585_a6c07850dc7b_a1
-- name    : WilliamsonShmoys.finite_graph_type_finite__p2m_cef71128_5f51_4c32_b585_a6c07850dc7b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:12:57.252654+00:00
-- url     : https://prove2.me/theorems/8b0bda3d-2683-4ebc-90c5-ecd8e38b7509
-- title:
--   Finiteness of graphs on a finite vertex type
-- statement:
--   The type of simple graphs on a finite vertex type is finite.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_graph_type_finite__p2m_cef71128_5f51_4c32_b585_a6c07850dc7b_a1 {V : Type} [Fintype V] : Finite (SimpleGraph V) := by sorry
