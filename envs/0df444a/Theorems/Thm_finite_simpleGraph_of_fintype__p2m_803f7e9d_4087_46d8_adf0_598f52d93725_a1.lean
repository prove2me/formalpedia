-- Prove2me | Theorems.Thm_finite_simpleGraph_of_fintype__p2m_803f7e9d_4087_46d8_adf0_598f52d93725_a1
-- name    : finite_simpleGraph_of_fintype__p2m_803f7e9d_4087_46d8_adf0_598f52d93725_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:30:12.509426+00:00
-- url     : https://prove2.me/theorems/55abb1dd-ab0f-49ce-b41f-b32ff874f1be
-- title:
--   Simple graphs on a finite vertex type form a finite type
-- statement:
--   For a finite vertex type, there are only finitely many simple graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_simpleGraph_of_fintype__p2m_803f7e9d_4087_46d8_adf0_598f52d93725_a1
    {V : Type} [Fintype V] : Finite (SimpleGraph V) := by sorry
