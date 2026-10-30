-- Prove2me | Theorems.Thm_finite_simplegraph__p2m_660d2f63_e4f8_48ad_a231_be9e34497c76_a1
-- name    : finite_simplegraph__p2m_660d2f63_e4f8_48ad_a231_be9e34497c76_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:05:32.038953+00:00
-- url     : https://prove2.me/theorems/f7affbf2-5c75-47e5-9f42-641d79530505
-- title:
--   Finiteness of simple graphs on a finite vertex type
-- statement:
--   The type of simple graphs on a finite vertex type is finite.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_simplegraph__p2m_660d2f63_e4f8_48ad_a231_be9e34497c76_a1 {V : Type} [Fintype V] : Finite (SimpleGraph V) := by sorry
