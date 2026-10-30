-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_predicate_maximal_supergraph_exists__p2m_a41ba058_0926_4932_8131_302826679a62_a2
-- name    : WilliamsonShmoys.finite_predicate_maximal_supergraph_exists__p2m_a41ba058_0926_4932_8131_302826679a62_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:57:14.106158+00:00
-- url     : https://prove2.me/theorems/1ad6b705-d364-4275-b2a3-96584a53e419
-- title:
--   Maximal supergraph for a finite downward-closed graph property
-- statement:
--   For a finite vertex type, any graph satisfying a subgraph-closed property has a supergraph satisfying the property that is maximal among such supergraphs. Prove this by maximizing the number of edges among the finite nonempty set of qualifying supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_predicate_maximal_supergraph_exists__p2m_a41ba058_0926_4932_8131_302826679a62_a2
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hG : P G)
    (hdown : ∀ {A B : SimpleGraph V}, A ≤ B → P B → P A) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ P K ∧ ∀ H : SimpleGraph V, K ≤ H → P H → H ≤ K := by sorry
