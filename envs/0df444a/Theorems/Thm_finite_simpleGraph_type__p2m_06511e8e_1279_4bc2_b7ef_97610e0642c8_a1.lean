-- Prove2me | Theorems.Thm_finite_simpleGraph_type__p2m_06511e8e_1279_4bc2_b7ef_97610e0642c8_a1
-- name    : finite_simpleGraph_type__p2m_06511e8e_1279_4bc2_b7ef_97610e0642c8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:02:24.118175+00:00
-- url     : https://prove2.me/theorems/886dc344-3f11-40ca-a092-1d08cef59a76
-- title:
--   Simple graphs on a finite vertex type form a finite type
-- statement:
--   There are only finitely many simple graphs on a finite vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_simpleGraph_type__p2m_06511e8e_1279_4bc2_b7ef_97610e0642c8_a1
    {V : Type} [Fintype V] : Finite (SimpleGraph V) := by sorry
