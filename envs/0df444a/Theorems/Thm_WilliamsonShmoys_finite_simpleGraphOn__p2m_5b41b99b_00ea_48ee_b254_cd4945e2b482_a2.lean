-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simpleGraphOn__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a2
-- name    : WilliamsonShmoys.finite_simpleGraphOn__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:18:56.411836+00:00
-- url     : https://prove2.me/theorems/f02c58ed-d1d4-4823-bfad-8b095aada63f
-- title:
--   Finiteness of simple graphs on a finite vertex type
-- statement:
--   There are finitely many simple graphs on a finite vertex type, since each graph is determined by its adjacency relation on the finite pair type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_simpleGraphOn__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a2
    {V : Type} [Fintype V] [LinearOrder V] : Finite (SimpleGraph V) := by sorry
