-- Prove2me | Theorems.Thm_finite_maximal_simpleGraph_extension__p2m_eb256fa3_9e89_4cdb_b978_02905f819491_a1
-- name    : finite_maximal_simpleGraph_extension__p2m_eb256fa3_9e89_4cdb_b978_02905f819491_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:38:59.436337+00:00
-- url     : https://prove2.me/theorems/a10335eb-4418-4032-b49f-d3c3f6c6ba7f
-- title:
--   Finite maximal extension for a graph predicate
-- statement:
--   For any finite vertex type, any property of simple graphs, and any graph H satisfying that property, there is a maximal graph satisfying the property among the supergraphs of H.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_maximal_simpleGraph_extension__p2m_eb256fa3_9e89_4cdb_b978_02905f819491_a1
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ P K ∧
        ∀ L : SimpleGraph V, K ≤ L → P L → L = K := by sorry
