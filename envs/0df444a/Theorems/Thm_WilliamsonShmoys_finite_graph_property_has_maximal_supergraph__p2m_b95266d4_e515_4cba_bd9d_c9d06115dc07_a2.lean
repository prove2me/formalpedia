-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_property_has_maximal_supergraph__p2m_b95266d4_e515_4cba_bd9d_c9d06115dc07_a2
-- name    : WilliamsonShmoys.finite_graph_property_has_maximal_supergraph__p2m_b95266d4_e515_4cba_bd9d_c9d06115dc07_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:33:08.668902+00:00
-- url     : https://prove2.me/theorems/a7e19560-177e-4afe-bc74-64e7539901ce
-- title:
--   Finite graph properties admit maximal supergraphs
-- statement:
--   For a finite linearly ordered vertex type, any graph satisfying a property has a supergraph satisfying that property which is maximal among such supergraphs. The statement does not require monotonicity or decidability of the property: it only selects among the supergraphs that satisfy it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_graph_property_has_maximal_supergraph__p2m_b95266d4_e515_4cba_bd9d_c9d06115dc07_a2 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V → Prop) (K : SimpleGraph V) (hK : P K) : ∃ H : SimpleGraph V, K ≤ H ∧ P H ∧ ∀ J : SimpleGraph V, H ≤ J → P J → J = H := by sorry
