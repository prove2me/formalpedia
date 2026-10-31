-- Prove2me | Theorems.Thm_exists_maximal_supergraph_of_hereditary_property__p2m_4d37fe7f_2e72_452b_8439_d9da71f76f12_a2
-- name    : exists_maximal_supergraph_of_hereditary_property__p2m_4d37fe7f_2e72_452b_8439_d9da71f76f12_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:04:13.888138+00:00
-- url     : https://prove2.me/theorems/a5ada2d3-7545-41d8-8089-bb59e4274a4d
-- title:
--   Finite maximal extension for hereditary graph properties
-- statement:
--   On a finite vertex type, a graph satisfying an edge-hereditary property has a supergraph satisfying that property which is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_maximal_supergraph_of_hereditary_property__p2m_4d37fe7f_2e72_452b_8439_d9da71f76f12_a2
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (K : SimpleGraph V)
    (hK : P K)
    (hhered : ∀ G H : SimpleGraph V, H.edgeSet ⊆ G.edgeSet → P G → P H) :
    ∃ N : SimpleGraph V,
      K.edgeSet ⊆ N.edgeSet ∧
      P N ∧
      ∀ M : SimpleGraph V,
        N.edgeSet ⊆ M.edgeSet →
        P M →
        M.edgeSet = N.edgeSet := by sorry
