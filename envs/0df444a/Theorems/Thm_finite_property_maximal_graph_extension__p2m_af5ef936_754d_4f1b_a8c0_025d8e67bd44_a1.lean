-- Prove2me | Theorems.Thm_finite_property_maximal_graph_extension__p2m_af5ef936_754d_4f1b_a8c0_025d8e67bd44_a1
-- name    : finite_property_maximal_graph_extension__p2m_af5ef936_754d_4f1b_a8c0_025d8e67bd44_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:40:31.19434+00:00
-- url     : https://prove2.me/theorems/cff2ce8c-e80b-4bb3-a446-1b34a17c7175
-- title:
--   Finite maximal extension for a graph property
-- statement:
--   For a finite vertex type, every graph satisfying any property has a property-satisfying supergraph that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_property_maximal_graph_extension__p2m_af5ef936_754d_4f1b_a8c0_025d8e67bd44_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (G : SimpleGraph V)
    (hG : P G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      P H ∧
      ∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet →
        P K →
        H.edgeSet = K.edgeSet := by sorry
