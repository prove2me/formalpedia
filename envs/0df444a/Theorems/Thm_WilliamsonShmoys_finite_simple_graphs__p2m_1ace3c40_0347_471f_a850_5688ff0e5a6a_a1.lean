-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simple_graphs__p2m_1ace3c40_0347_471f_a850_5688ff0e5a6a_a1
-- name    : WilliamsonShmoys.finite_simple_graphs__p2m_1ace3c40_0347_471f_a850_5688ff0e5a6a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:50:01.595985+00:00
-- url     : https://prove2.me/theorems/c82a77e4-bc5d-4130-a040-61198e715a58
-- title:
--   Simple graphs on a finite vertex type form a finite type
-- statement:
--   If the vertex type is finite, then the type of simple graphs on those vertices is finite.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_simple_graphs__p2m_1ace3c40_0347_471f_a850_5688ff0e5a6a_a1
    {V : Type} [Fintype V] :
    Finite (SimpleGraph V) := by sorry
