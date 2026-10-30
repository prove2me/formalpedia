-- Prove2me | Theorems.Thm_finite_simpleGraph_maximal_supergraph__p2m_8526028d_6503_4baf_b95b_7d2634d3c3de_a1
-- name    : finite_simpleGraph_maximal_supergraph__p2m_8526028d_6503_4baf_b95b_7d2634d3c3de_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:23:58.530814+00:00
-- url     : https://prove2.me/theorems/611a5fc7-8dbb-464d-bb32-92b0d998f88e
-- title:
--   Finite maximal supergraph for a graph property
-- statement:
--   For any property of simple graphs on a finite linearly ordered vertex type, every graph satisfying the property has a supergraph satisfying it that is maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem finite_simpleGraph_maximal_supergraph__p2m_8526028d_6503_4baf_b95b_7d2634d3c3de_a1 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V → Prop) (L : SimpleGraph V) (hL : P L) : ∃ K : SimpleGraph V, L ≤ K ∧ P K ∧ (∀ H : SimpleGraph V, K ≤ H → P H → H ≤ K) := by sorry
