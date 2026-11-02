-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite__p2m_f4b47241_0114_4ac8_84bb_0550b2f73838_a1
-- name    : WilliamsonShmoys.exists_maximal_supergraph_of_finite__p2m_f4b47241_0114_4ac8_84bb_0550b2f73838_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:35:10.459298+00:00
-- url     : https://prove2.me/theorems/eb94990a-d06d-4396-9fc2-71f406ba8cd7
-- title:
--   Finite maximality for graph predicates
-- statement:
--   For any predicate on simple graphs over a finite vertex type, every graph satisfying the predicate has a predicate-satisfying supergraph that is maximal under inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximal_supergraph_of_finite__p2m_f4b47241_0114_4ac8_84bb_0550b2f73838_a1
    {V : Type} [Fintype V]
    (H : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P H) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
    ∃ K : SimpleGraph V, H ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L = K := by sorry
