-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_type__p2m_bf001e0e_24f9_43c1_8004_bdc368085703_a1
-- name    : WilliamsonShmoys.finite_simpleGraph_type__p2m_bf001e0e_24f9_43c1_8004_bdc368085703_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:01:52.535206+00:00
-- url     : https://prove2.me/theorems/1fd94671-f610-48c2-9e21-c1acc3af37b7
-- title:
--   Graphs on a finite vertex type form a finite type
-- statement:
--   For a finite vertex type with decidable equality, there are only finitely many simple graphs on that type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_simpleGraph_type__p2m_bf001e0e_24f9_43c1_8004_bdc368085703_a1 {V : Type} [Fintype V] [DecidableEq V] : Finite (SimpleGraph V) := by sorry
