-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph_of_downward_property__p2m_b2333537_9e91_4fe0_a355_0d6ef469faac_a1
-- name    : WilliamsonShmoys.finite_maximal_supergraph_of_downward_property__p2m_b2333537_9e91_4fe0_a355_0d6ef469faac_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:48:03.825224+00:00
-- url     : https://prove2.me/theorems/47df9746-7a0a-41a7-915b-e40dd19dfc71
-- title:
--   Finite maximal extension for a hereditary graph property
-- statement:
--   For a finite vertex type, any graph satisfying an edge-deletion-hereditary property is contained in a supergraph satisfying that property which is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_supergraph_of_downward_property__p2m_b2333537_9e91_4fe0_a355_0d6ef469faac_a1
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hK : P K)
    (hdown : ∀ {G H : SimpleGraph V},
      (∀ u v, G.Adj u v → H.Adj u v) → P H → P G) :
    ∃ M : SimpleGraph V,
      (∀ u v, K.Adj u v → M.Adj u v) ∧
      P M ∧
      (∀ N : SimpleGraph V,
        (∀ u v, M.Adj u v → N.Adj u v) →
        P N →
        (∀ u v, N.Adj u v → M.Adj u v)) := by sorry
