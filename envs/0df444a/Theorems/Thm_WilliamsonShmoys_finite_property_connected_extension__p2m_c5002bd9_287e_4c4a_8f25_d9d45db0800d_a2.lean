-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_property_connected_extension__p2m_c5002bd9_287e_4c4a_8f25_d9d45db0800d_a2
-- name    : WilliamsonShmoys.finite_property_connected_extension__p2m_c5002bd9_287e_4c4a_8f25_d9d45db0800d_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T01:02:35.273978+00:00
-- url     : https://prove2.me/theorems/eb929d3d-412f-49f7-ad86-3f0f4e3e928c
-- title:
--   Finite strict edge growth yields a connected extension
-- statement:
--   On a finite vertex type, a graph property that permits strict edge-count growth whenever a graph with the property is disconnected has a connected supergraph with the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_property_connected_extension__p2m_c5002bd9_287e_4c4a_8f25_d9d45db0800d_a2
    {V : Type} [Fintype V] (T : SimpleGraph V)
    (P : SimpleGraph V → Prop) (hT : P T)
    (hstep : ∀ G : SimpleGraph V, P G → ¬ G.Connected →
      ∃ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet ∧ P H ∧
        Nat.card G.edgeSet < Nat.card H.edgeSet) :
    ∃ H : SimpleGraph V, T.edgeSet ⊆ H.edgeSet ∧ P H ∧ H.Connected := by sorry
