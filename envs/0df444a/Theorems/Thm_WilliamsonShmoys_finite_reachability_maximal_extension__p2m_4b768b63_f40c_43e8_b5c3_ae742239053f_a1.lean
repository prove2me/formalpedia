-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_reachability_maximal_extension__p2m_4b768b63_f40c_43e8_b5c3_ae742239053f_a1
-- name    : WilliamsonShmoys.finite_reachability_maximal_extension__p2m_4b768b63_f40c_43e8_b5c3_ae742239053f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:45:28.711001+00:00
-- url     : https://prove2.me/theorems/eb23799a-bc1f-4792-8bfa-322f1a36050a
-- title:
--   Finite maximality of reachable pairs among extensions
-- statement:
--   Among the predicate-preserving supergraphs of a finite graph whose edge count is at least the original’s, there is one whose reachable ordered pairs cannot be strictly enlarged by any other qualifying graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_reachability_maximal_extension__p2m_4b768b63_f40c_43e8_b5c3_ae742239053f_a1 {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hP : P G) : ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard ∧ (∀ K : SimpleGraph V, G ≤ K → P K → G.edgeSet.ncard ≤ K.edgeSet.ncard → (∀ u v, H.Reachable u v → K.Reachable u v) → ∀ u v, K.Reachable u v → H.Reachable u v) := by sorry
