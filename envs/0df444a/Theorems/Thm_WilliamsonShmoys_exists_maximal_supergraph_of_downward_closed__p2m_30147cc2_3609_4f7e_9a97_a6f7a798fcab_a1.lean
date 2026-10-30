-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_downward_closed__p2m_30147cc2_3609_4f7e_9a97_a6f7a798fcab_a1
-- name    : WilliamsonShmoys.exists_maximal_supergraph_of_downward_closed__p2m_30147cc2_3609_4f7e_9a97_a6f7a798fcab_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:59:42.691996+00:00
-- url     : https://prove2.me/theorems/fb7ca16b-7862-407e-9a6d-3b14484e60e3
-- title:
--   Finite maximal supergraph for a downward-closed property
-- statement:
--   For any downward-closed property on graphs over a finite ordered vertex type, every graph satisfying the property has a supergraph satisfying it whose edge count is at least as large and which has no strictly larger supergraph satisfying the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximal_supergraph_of_downward_closed__p2m_30147cc2_3609_4f7e_9a97_a6f7a798fcab_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ ⦃A B : SimpleGraph V⦄, A ≤ B → P B → P A)
    (G : SimpleGraph V) (hG : P G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ P H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ K : SimpleGraph V, H ≤ K → P K → K ≤ H) := by sorry
