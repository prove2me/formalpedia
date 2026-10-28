-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph_of_subgraph_closed
-- name    : WilliamsonShmoys.finite_maximal_supergraph_of_subgraph_closed
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:25:30.385039+00:00
-- url     : https://prove2.me/theorems/5bee25ba-5532-4660-b97d-f61ec2e3f354
-- title:
--   Finite maximal extension for a subgraph-closed property
-- statement:
--   Every graph satisfying a subgraph-closed property on a finite ordered vertex type has a supergraph satisfying that property which is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_supergraph_of_subgraph_closed
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hclosed : ∀ ⦃G H : SimpleGraph V⦄, G ≤ H → P H → P G)
    (M : SimpleGraph V) (hM : P M) :
    ∃ Pgraph : SimpleGraph V, M ≤ Pgraph ∧ P Pgraph ∧
      ∀ Q : SimpleGraph V, Pgraph ≤ Q → P Q → Q = Pgraph := by sorry
