-- Prove2me | Theorems.Thm_finite_simpleGraph_maximal_supergraph__p2m_1841e8f3_3dc0_4413_8d65_8f642645b455_a2
-- name    : finite_simpleGraph_maximal_supergraph__p2m_1841e8f3_3dc0_4413_8d65_8f642645b455_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:11:55.589225+00:00
-- url     : https://prove2.me/theorems/97201ef7-2c0d-4857-863f-b6e29a4a7f08
-- title:
--   Finite maximal extension for a graph property
-- statement:
--   On a finite vertex type, every graph satisfying a property has a supergraph satisfying that property which is maximal among supergraphs satisfying it. The property need not hold for all supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_simpleGraph_maximal_supergraph__p2m_1841e8f3_3dc0_4413_8d65_8f642645b455_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P G) : Exists fun K : SimpleGraph V => And (LE.le G K) (And (P K) (∀ L : SimpleGraph V, LE.le K L → P L → LE.le L K)) := by sorry
