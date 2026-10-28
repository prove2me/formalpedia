-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_of_fintype
-- name    : WilliamsonShmoys.finite_simpleGraph_of_fintype
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:42:58.038082+00:00
-- url     : https://prove2.me/theorems/f3891109-56f6-434a-81ce-15e7704ed3bb
-- title:
--   Finiteness of simple graphs on a finite vertex type
-- statement:
--   The type of simple graphs on a finite vertex type is finite.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_simpleGraph_of_fintype
    {V : Type} [Fintype V] : Finite (SimpleGraph V) := by sorry
