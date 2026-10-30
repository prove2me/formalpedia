-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_predicate_maximal_extension__p2m_03e90475_cbaa_4d30_84cc_f87b4a621968_a1
-- name    : WilliamsonShmoys.finite_planar_predicate_maximal_extension__p2m_03e90475_cbaa_4d30_84cc_f87b4a621968_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:54:04.656986+00:00
-- url     : https://prove2.me/theorems/cf3a7518-52ee-4311-91e1-f97b1622bde0
-- title:
--   Maximal extension for a hereditary predicate on finite graphs
-- statement:
--   For a finite vertex type, any graph satisfying a predicate inherited by subgraphs has an extension satisfying the predicate that is maximal among such extensions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_planar_predicate_maximal_extension__p2m_03e90475_cbaa_4d30_84cc_f87b4a621968_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G)
    (K : SimpleGraph V) (hK : P K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ P L ∧
      ∀ M : SimpleGraph V, L ≤ M → P M → M ≤ L := by sorry
