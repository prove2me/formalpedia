-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_edge_augmentation__p2m_460389d4_31bd_4508_b209_05dd70a4382c_a1
-- name    : WilliamsonShmoys.finite_edge_augmentation__p2m_460389d4_31bd_4508_b209_05dd70a4382c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:08:22.616106+00:00
-- url     : https://prove2.me/theorems/5eacf842-b74c-4979-8391-5d0083447751
-- title:
--   Finite augmentation under an arbitrary graph property
-- statement:
--   For any property of finite graphs, if every disconnected supergraph satisfying that property can be augmented by an exact edge addition between unreachable distinct vertices while preserving the property, then some connected supergraph also satisfies the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_edge_augmentation__p2m_460389d4_31bd_4508_b209_05dd70a4382c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (G : SimpleGraph V) (hG : P G)
    (hstep : ∀ (H : SimpleGraph V), G ≤ H → P H → ¬ H.Connected →
      ∃ (u v : V) (huv : u ≠ v),
        ¬ H.Reachable u v ∧
        ∃ K : SimpleGraph V,
          H ≤ K ∧ P K ∧
          ∀ a b, K.Adj a b ↔
            H.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u)) :
    ∃ C : SimpleGraph V, G ≤ C ∧ C.Connected ∧ P C := by sorry
