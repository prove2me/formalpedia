-- Prove2me | Theorems.Thm_finite_simpleGraph__p2m_038327fe_4daf_4028_a7aa_65aa49782279_a1
-- name    : finite_simpleGraph__p2m_038327fe_4daf_4028_a7aa_65aa49782279_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T20:56:04.936986+00:00
-- url     : https://prove2.me/theorems/3458ed73-2083-463b-a588-198dc9d828d9
-- title:
--   Finiteness of simple graphs on a finite vertex type
-- statement:
--   There are only finitely many simple graphs on a finite vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_simpleGraph__p2m_038327fe_4daf_4028_a7aa_65aa49782279_a1 {V : Type} [Fintype V] : Finite (SimpleGraph V) := by sorry
