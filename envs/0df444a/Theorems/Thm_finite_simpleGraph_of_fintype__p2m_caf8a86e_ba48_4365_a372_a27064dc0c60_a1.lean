-- Prove2me | Theorems.Thm_finite_simpleGraph_of_fintype__p2m_caf8a86e_ba48_4365_a372_a27064dc0c60_a1
-- name    : finite_simpleGraph_of_fintype__p2m_caf8a86e_ba48_4365_a372_a27064dc0c60_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:32:14.299537+00:00
-- url     : https://prove2.me/theorems/29922c36-ee90-4efe-8688-2864169d6614
-- title:
--   Finite graph type on finite vertices
-- statement:
--   The type of simple graphs on a finite vertex type is finite.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_simpleGraph_of_fintype__p2m_caf8a86e_ba48_4365_a372_a27064dc0c60_a1
    {V : Type} [Fintype V] : Finite (SimpleGraph V) := by sorry
