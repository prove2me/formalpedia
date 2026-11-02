-- Prove2me | Theorems.Thm_finite_simpleGraph_universe__p2m_9e5fb9d2_aa0e_41c4_9a80_cb078400c4e8_a1
-- name    : finite_simpleGraph_universe__p2m_9e5fb9d2_aa0e_41c4_9a80_cb078400c4e8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:48:11.002735+00:00
-- url     : https://prove2.me/theorems/efd8715e-c4e4-4e5c-8ae9-418a0c57c033
-- title:
--   Finite universe of simple graphs on finite vertices
-- statement:
--   The type of simple graphs on a finite vertex type is finite. This supplies the finite search space used by the parent proof. An independent route is to encode each graph by its Boolean adjacency table, show this encoding is injective by extensionality, and use finiteness of the function space on finite V.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_simpleGraph_universe__p2m_9e5fb9d2_aa0e_41c4_9a80_cb078400c4e8_a1 {V : Type} [Fintype V] : Finite (SimpleGraph V) := by sorry
