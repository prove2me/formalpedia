-- Prove2me | Theorems.Thm_exists_edge_maximal_subgraph_above__p2m_8f0c4e79_82ed_4eab_8262_744ee1ed1865_a1
-- name    : exists_edge_maximal_subgraph_above__p2m_8f0c4e79_82ed_4eab_8262_744ee1ed1865_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T19:48:31.564545+00:00
-- url     : https://prove2.me/theorems/660d2f63-e4f8-48ad-a231-be9e34497c76
-- title:
--   Finite maximal extension for downward-closed graph predicates
-- statement:
--   Given a finite linearly ordered vertex type and a graph predicate closed under removing edges, any graph satisfying the predicate has a supergraph satisfying it that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_edge_maximal_subgraph_above__p2m_8f0c4e79_82ed_4eab_8262_744ee1ed1865_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hK : P K)
    (hdown : ∀ G H : SimpleGraph V,
      H.edgeSet ⊆ G.edgeSet → P G → P H) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      P L ∧
      ∀ M : SimpleGraph V,
        L.edgeSet ⊆ M.edgeSet →
        P M →
        M.edgeSet ⊆ L.edgeSet := by sorry
