-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_edge_augmentation_completion__p2m_f3f359af_2762_432f_8e05_8cdbcb14d938_a2
-- name    : WilliamsonShmoys.finite_edge_augmentation_completion__p2m_f3f359af_2762_432f_8e05_8cdbcb14d938_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:28:21.486981+00:00
-- url     : https://prove2.me/theorems/2276ad68-a381-4c3d-9dc8-9b17a25ea0f2
-- title:
--   Finite completion from one-edge augmentation
-- statement:
--   Given a property of finite graphs, a bound on the starting edge count, and a property-preserving extension that adds exactly one edge whenever the count is below a target, finitely many extensions produce a graph with exactly the target edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_edge_augmentation_completion__p2m_f3f359af_2762_432f_8e05_8cdbcb14d938_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (G : SimpleGraph V)
    (m : ℕ)
    (hP : P G)
    (hBound : G.edgeSet.ncard ≤ m)
    (hAugment : ∀ K : SimpleGraph V, P K → K.edgeSet.ncard < m →
      ∃ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet ∧
        L.edgeSet.ncard = K.edgeSet.ncard + 1 ∧
        P L) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      H.edgeSet.ncard = m ∧
      P H := by sorry
