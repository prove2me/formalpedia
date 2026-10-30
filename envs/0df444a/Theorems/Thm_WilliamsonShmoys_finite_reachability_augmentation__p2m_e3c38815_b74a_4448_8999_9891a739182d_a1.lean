-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_reachability_augmentation__p2m_e3c38815_b74a_4448_8999_9891a739182d_a1
-- name    : WilliamsonShmoys.finite_reachability_augmentation__p2m_e3c38815_b74a_4448_8999_9891a739182d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:41:49.535821+00:00
-- url     : https://prove2.me/theorems/4b768b63-f40c-43e8-b5c3-ae742239053f
-- title:
--   Finite iteration of reachability-increasing extensions
-- statement:
--   On a finite vertex type, if every disconnected graph satisfying a predicate has a predicate-preserving extension that does not decrease the edge count and makes some new pair reachable while preserving old reachability, then there is a connected extension satisfying the predicate and with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_reachability_augmentation__p2m_e3c38815_b74a_4448_8999_9891a739182d_a1 {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hP : P G) (hStep : ∀ K : SimpleGraph V, P K → ¬ K.Connected → ∃ K' : SimpleGraph V, K ≤ K' ∧ P K' ∧ K.edgeSet.ncard ≤ K'.edgeSet.ncard ∧ (∀ u v, K.Reachable u v → K'.Reachable u v) ∧ (∃ u v, ¬ K.Reachable u v ∧ K'.Reachable u v)) : ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧ H.Connected ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
