-- Prove2me | Theorems.Thm_finite_graph_has_maximal_extension__p2m_59758877_c28f_4756_a5bc_fc8ad3e95fc8_a1
-- name    : finite_graph_has_maximal_extension__p2m_59758877_c28f_4756_a5bc_fc8ad3e95fc8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:52:53.318173+00:00
-- url     : https://prove2.me/theorems/ccc1f7fb-8562-47c4-8309-e5694c4cbdef
-- title:
--   A finite graph property has a maximal supergraph extension
-- statement:
--   For a finite vertex type, any graph satisfying P has a P-preserving supergraph that is maximal among P-preserving supergraphs of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_graph_has_maximal_extension__p2m_59758877_c28f_4756_a5bc_fc8ad3e95fc8_a1
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop) (K : SimpleGraph V) (hK : P K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ P H ∧
      ∀ G : SimpleGraph V, K ≤ G → P G → ¬ H < G := by sorry
