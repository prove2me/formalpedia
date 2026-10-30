-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_predicate_supergraph_finite__p2m_90cbbd5c_48b8_4938_99ca_cd8db48989ee_a1
-- name    : WilliamsonShmoys.exists_maximal_predicate_supergraph_finite__p2m_90cbbd5c_48b8_4938_99ca_cd8db48989ee_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T13:04:14.162579+00:00
-- url     : https://prove2.me/theorems/e0d8e8f1-2f24-43ae-bfc2-8d16d27ed67e
-- title:
--   Finite maximal extension for a hereditary graph property
-- statement:
--   On a finite vertex type, every graph satisfying an edge-subgraph-hereditary property has a supergraph satisfying that property which is maximal among such supergraphs on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximal_predicate_supergraph_finite__p2m_90cbbd5c_48b8_4938_99ca_cd8db48989ee_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hP : ∀ {A B : SimpleGraph V},
      Set.Subset A.edgeSet B.edgeSet → P B → P A)
    (G : SimpleGraph V)
    (hG : P G) :
    ∃ K : SimpleGraph V,
      Set.Subset G.edgeSet K.edgeSet ∧
      P K ∧
      ∀ L : SimpleGraph V,
        Set.Subset K.edgeSet L.edgeSet →
        P L →
        K.edgeSet = L.edgeSet := by sorry
