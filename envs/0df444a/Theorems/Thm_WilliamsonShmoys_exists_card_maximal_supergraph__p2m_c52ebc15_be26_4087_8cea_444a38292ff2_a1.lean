-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_card_maximal_supergraph__p2m_c52ebc15_be26_4087_8cea_444a38292ff2_a1
-- name    : WilliamsonShmoys.exists_card_maximal_supergraph__p2m_c52ebc15_be26_4087_8cea_444a38292ff2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:12:35.957122+00:00
-- url     : https://prove2.me/theorems/9a036de1-a38a-4618-915b-a37b06c19633
-- title:
--   Finite maximal supergraph for any property
-- statement:
--   For a finite vertex type, any property satisfied by a graph N admits a supergraph H satisfying that property such that H is maximal by edge inclusion among graphs with the property and has at least as many edges as N.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_card_maximal_supergraph__p2m_c52ebc15_be26_4087_8cea_444a38292ff2_a1
    {V : Type} [Fintype V]
    (N : SimpleGraph V) (P : SimpleGraph V → Prop) (hN : P N) :
    ∃ H : SimpleGraph V,
      N.edgeSet ⊆ H.edgeSet ∧ P H ∧
      (∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet → P K → K.edgeSet ⊆ H.edgeSet) ∧
      N.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
