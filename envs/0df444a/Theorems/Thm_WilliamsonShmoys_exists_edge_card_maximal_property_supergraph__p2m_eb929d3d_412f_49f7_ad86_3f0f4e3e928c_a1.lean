-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_card_maximal_property_supergraph__p2m_eb929d3d_412f_49f7_ad86_3f0f4e3e928c_a1
-- name    : WilliamsonShmoys.exists_edge_card_maximal_property_supergraph__p2m_eb929d3d_412f_49f7_ad86_3f0f4e3e928c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:22:54.836652+00:00
-- url     : https://prove2.me/theorems/17d920dd-140a-452f-86a6-d8bf52a4ecb5
-- title:
--   A property-preserving supergraph with maximal edge count
-- statement:
--   Among the property-preserving supergraphs of T, there is one whose edge count cannot be strictly increased by passing to another property-preserving supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_card_maximal_property_supergraph__p2m_eb929d3d_412f_49f7_ad86_3f0f4e3e928c_a1
    {V : Type} [Fintype V] (T : SimpleGraph V)
    (P : SimpleGraph V → Prop) (hT : P T) :
    ∃ G : SimpleGraph V, T.edgeSet ⊆ G.edgeSet ∧ P G ∧
      ∀ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet → P H →
        ¬ Nat.card G.edgeSet < Nat.card H.edgeSet := by sorry
