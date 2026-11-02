-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_predicate__p2m_d833d204_1cac_48ce_b1ff_fc91bbaabed8_a2
-- name    : WilliamsonShmoys.exists_maximal_supergraph_for_predicate__p2m_d833d204_1cac_48ce_b1ff_fc91bbaabed8_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:38:49.188672+00:00
-- url     : https://prove2.me/theorems/85bdf8cc-e400-4cd3-8ef7-5dedcf811cea
-- title:
--   Finite predicate-maximal supergraph
-- statement:
--   Every graph satisfying a predicate on simple graphs over a finite linearly ordered vertex type has a supergraph satisfying that predicate which is maximal among qualifying supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_for_predicate__p2m_d833d204_1cac_48ce_b1ff_fc91bbaabed8_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (L : SimpleGraph V) (hL : P L) :
    ∃ H : SimpleGraph V, L ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by sorry
