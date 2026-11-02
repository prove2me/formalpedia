-- Prove2me | Theorems.Thm_exists_maximal_property_supergraph__p2m_bde7bab7_9900_4674_96b7_2eea7887c7cc_a1
-- name    : exists_maximal_property_supergraph__p2m_bde7bab7_9900_4674_96b7_2eea7887c7cc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:15:24.885837+00:00
-- url     : https://prove2.me/theorems/af36c0ea-b2ee-41da-b6f6-c03e3b61807f
-- title:
--   A finite graph has a maximal supergraph satisfying any witnessed property
-- statement:
--   For any property of finite simple graphs, if a graph G has that property, then G has a supergraph H with the property that is maximal among the property-satisfying supergraphs of G.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_maximal_property_supergraph__p2m_bde7bab7_9900_4674_96b7_2eea7887c7cc_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (G : SimpleGraph V)
    (hG : P G) :
    ∃ H : SimpleGraph V,
      (∀ u v : V, G.Adj u v → H.Adj u v) ∧
      P H ∧
      (∀ K : SimpleGraph V,
        (∀ u v : V, G.Adj u v → K.Adj u v) →
        P K →
        (∀ u v : V, H.Adj u v → K.Adj u v) →
        K = H) := by sorry
