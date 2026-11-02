-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_property__p2m_b05574a0_b431_4a4f_aba2_4718b07b1171_a1
-- name    : WilliamsonShmoys.exists_maximal_supergraph_for_property__p2m_b05574a0_b431_4a4f_aba2_4718b07b1171_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:00:44.266511+00:00
-- url     : https://prove2.me/theorems/25e35176-a31f-4f4d-b529-6dfe245bf469
-- title:
--   Finite maximal supergraph for an arbitrary property
-- statement:
--   For any property of simple graphs on a finite linearly ordered vertex type, if H satisfies the property then H has a supergraph satisfying it whose edge count is at least that of H and which has no strictly larger feasible supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_for_property__p2m_b05574a0_b431_4a4f_aba2_4718b07b1171_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V)
    (hP : P H) :
    ∃ M : SimpleGraph V,
      H ≤ M ∧
      P M ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       letI : DecidableRel M.Adj := Classical.decRel M.Adj
       H.edgeFinset.card ≤ M.edgeFinset.card) ∧
      (∀ N : SimpleGraph V, M ≤ N → P N → N ≤ M) := by sorry
