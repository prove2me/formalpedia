-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_property_maximal_extension__p2m_f1c70f2e_734a_4ab3_9ef1_4b1e0b3c2cfc_a1
-- name    : WilliamsonShmoys.finite_graph_property_maximal_extension__p2m_f1c70f2e_734a_4ab3_9ef1_4b1e0b3c2cfc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:10:59.382514+00:00
-- url     : https://prove2.me/theorems/3dd2f00a-a125-4333-88d9-0f94f3546b41
-- title:
--   Finite graph properties admit maximal extensions
-- statement:
--   For any property of graphs on a finite linearly ordered vertex type, every graph satisfying the property has a supergraph satisfying it that is maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

open SimpleGraph

theorem WilliamsonShmoys.finite_graph_property_maximal_extension__p2m_f1c70f2e_734a_4ab3_9ef1_4b1e0b3c2cfc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (H : SimpleGraph V) (hH : P H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L = K := by sorry
