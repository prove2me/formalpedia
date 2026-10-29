-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_supergraph_maximal_for_predicate__p2m_c813e8d9_188c_4202_b644_d7aaf9123e11_a1
-- name    : WilliamsonShmoys.exists_supergraph_maximal_for_predicate__p2m_c813e8d9_188c_4202_b644_d7aaf9123e11_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:48:04.767786+00:00
-- url     : https://prove2.me/theorems/db8cc9f9-84ab-47b1-987d-14abeeb1cf2c
-- title:
--   Finite maximality for graph predicates
-- statement:
--   For any predicate on simple graphs over a finite linearly ordered vertex type, if the predicate holds of a graph M, then M has a predicate-satisfying supergraph that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_supergraph_maximal_for_predicate__p2m_c813e8d9_188c_4202_b644_d7aaf9123e11_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hM : P M) :
    ∃ N : SimpleGraph V,
      Set.Subset M.edgeSet N.edgeSet ∧
      P N ∧
      ∀ Q : SimpleGraph V,
        Set.Subset N.edgeSet Q.edgeSet →
        P Q →
        Set.Subset Q.edgeSet N.edgeSet := by sorry
