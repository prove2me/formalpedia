-- Prove2me | Theorems.Thm_finite_graph_property_has_maximal_extension__p2m_6822b8c0_b310_4ef6_afea_d822182653e7_a1
-- name    : finite_graph_property_has_maximal_extension__p2m_6822b8c0_b310_4ef6_afea_d822182653e7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:15:19.100628+00:00
-- url     : https://prove2.me/theorems/8270b3b6-14ed-48d1-9b5b-0f0ce1f377bd
-- title:
--   Finite graph properties have maximal extensions
-- statement:
--   On a fixed finite linearly ordered vertex type, any graph satisfying a subgraph-closed property has an extension that is maximal among graphs satisfying that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_graph_property_has_maximal_extension__p2m_6822b8c0_b310_4ef6_afea_d822182653e7_a1
    (V : Type) [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hmono : ∀ {G F : SimpleGraph V}, G ≤ F → P F → P G)
    (H : SimpleGraph V) (hH : P H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ P K ∧
        (∀ L : SimpleGraph V, K ≤ L → P L → L = K) := by sorry
