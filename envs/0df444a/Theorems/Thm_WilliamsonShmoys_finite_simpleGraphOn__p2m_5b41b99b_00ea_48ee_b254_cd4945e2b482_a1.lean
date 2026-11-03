-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simpleGraphOn__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a1
-- name    : WilliamsonShmoys.finite_simpleGraphOn__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:11:02.7471+00:00
-- url     : https://prove2.me/theorems/d5b488b6-fb1f-4218-afdd-fc7b5dcf3741
-- title:
--   Finiteness of simple graphs on a finite vertex type
-- statement:
--   There are only finitely many simple graphs on a finite vertex type. Encode each graph by its adjacency relation, a function from the finite pair type to the finite type Prop, and use injectivity of this encoding.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_simpleGraphOn__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a1
    {V : Type} [Fintype V] [LinearOrder V] : Finite (SimpleGraph V) := by sorry
