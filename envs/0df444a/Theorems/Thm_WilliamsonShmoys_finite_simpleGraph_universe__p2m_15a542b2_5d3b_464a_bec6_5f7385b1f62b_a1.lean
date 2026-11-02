-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_universe__p2m_15a542b2_5d3b_464a_bec6_5f7385b1f62b_a1
-- name    : WilliamsonShmoys.finite_simpleGraph_universe__p2m_15a542b2_5d3b_464a_bec6_5f7385b1f62b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:31:34.709101+00:00
-- url     : https://prove2.me/theorems/9d52c9f1-d5c0-46dd-a1b0-3d56704c6841
-- title:
--   Finiteness of simple graphs on a finite vertex type
-- statement:
--   The type of simple graphs on a finite vertex type is finite. Encode each graph by its Boolean adjacency matrix; symmetry and irreflexivity only restrict the possible matrices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_simpleGraph_universe__p2m_15a542b2_5d3b_464a_bec6_5f7385b1f62b_a1
    {V : Type} [Fintype V] : Finite (SimpleGraph V) := by sorry
