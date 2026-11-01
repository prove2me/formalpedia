-- Prove2me | Theorems.Thm_finite_simpleGraph_type_is_finite__p2m_a10335eb_4418_4032_b49f_d3c3f6c6ba7f_a3
-- name    : finite_simpleGraph_type_is_finite__p2m_a10335eb_4418_4032_b49f_d3c3f6c6ba7f_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:49:53.942139+00:00
-- url     : https://prove2.me/theorems/0d66e520-1d0b-4203-9ed3-2ec80d8157a0
-- title:
--   Finiteness of simple graphs on a finite vertex type
-- statement:
--   If the vertex type is finite, the type of simple graphs on it is finite.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_simpleGraph_type_is_finite__p2m_a10335eb_4418_4032_b49f_d3c3f6c6ba7f_a3
    {V : Type} [Fintype V] :
    Finite (SimpleGraph V) := by sorry
