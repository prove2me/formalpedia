-- Prove2me | Theorems.Thm_finite_simpleGraph__p2m_0e06c23e_290e_423e_a5fe_9ac4288d0e45_a2
-- name    : finite_simpleGraph__p2m_0e06c23e_290e_423e_a5fe_9ac4288d0e45_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:32:34.307525+00:00
-- url     : https://prove2.me/theorems/7ab8b148-f910-42b9-a1fa-0da85e93733f
-- title:
--   Finiteness of simple graphs on a finite vertex type
-- statement:
--   The type of simple graphs on a finite vertex type is finite.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_simpleGraph__p2m_0e06c23e_290e_423e_a5fe_9ac4288d0e45_a2 {V : Type} [Fintype V] : Finite (SimpleGraph V) := by sorry
