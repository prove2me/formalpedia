-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_simpleGraph_supergraph_for__p2m_db589962_0581_431b_85a4_f73500e19284_a1
-- name    : WilliamsonShmoys.exists_maximal_simpleGraph_supergraph_for__p2m_db589962_0581_431b_85a4_f73500e19284_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:59:25.408481+00:00
-- url     : https://prove2.me/theorems/8775982d-ad40-466c-a67e-028ddae6eb66
-- title:
--   Finite maximal supergraph for an arbitrary graph property
-- statement:
--   For a finite vertex type, every graph satisfying a property P has a supergraph satisfying P that is maximal among P-supergraphs. No closure assumption on P is needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_simpleGraph_supergraph_for__p2m_db589962_0581_431b_85a4_f73500e19284_a1
    {V : Type} [Fintype V]
    (U : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P U) :
    ∃ W : SimpleGraph V, U ≤ W ∧ P W ∧
      ∀ X : SimpleGraph V, W ≤ X → P X → X ≤ W := by
  sorry
