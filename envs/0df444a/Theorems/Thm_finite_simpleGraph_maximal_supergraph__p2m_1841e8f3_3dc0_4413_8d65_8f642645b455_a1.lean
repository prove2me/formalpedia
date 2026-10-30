-- Prove2me | Theorems.Thm_finite_simpleGraph_maximal_supergraph__p2m_1841e8f3_3dc0_4413_8d65_8f642645b455_a1
-- name    : finite_simpleGraph_maximal_supergraph__p2m_1841e8f3_3dc0_4413_8d65_8f642645b455_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:09:01.378521+00:00
-- url     : https://prove2.me/theorems/fb02b1cf-9de2-4475-bf5d-05d90b1d6e99
-- title:
--   Finite maximal extension for a graph property
-- statement:
--   For a finite graph vertex type, if a graph satisfies a property and every supergraph of it satisfies that property, then it has a supergraph that is maximal among graphs satisfying the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_simpleGraph_maximal_supergraph__p2m_1841e8f3_3dc0_4413_8d65_8f642645b455_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P G) (hP_super : ∀ K : SimpleGraph V, LE.le G K → P K) : Exists fun K : SimpleGraph V => And (LE.le G K) (And (P K) (∀ L : SimpleGraph V, LE.le K L → P L → LE.le L K)) := by sorry
