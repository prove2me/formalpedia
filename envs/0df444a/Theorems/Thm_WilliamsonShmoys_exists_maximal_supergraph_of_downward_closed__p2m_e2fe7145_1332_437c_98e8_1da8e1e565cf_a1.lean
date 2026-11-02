-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_downward_closed__p2m_e2fe7145_1332_437c_98e8_1da8e1e565cf_a1
-- name    : WilliamsonShmoys.exists_maximal_supergraph_of_downward_closed__p2m_e2fe7145_1332_437c_98e8_1da8e1e565cf_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:36:31.361567+00:00
-- url     : https://prove2.me/theorems/e8f94df9-99d0-4990-ac26-f65682684e6a
-- title:
--   Finite maximal extension for a downward-closed graph property
-- statement:
--   For a finite vertex type, every graph satisfying a downward-closed property is contained in a graph satisfying the property that has no strictly larger graph with that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_of_downward_closed__p2m_e2fe7145_1332_437c_98e8_1da8e1e565cf_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {G H : SimpleGraph V}, G.edgeSet ⊆ H.edgeSet → P H → P G)
    (L : SimpleGraph V) (hL : P L) :
    ∃ K : SimpleGraph V, L.edgeSet ⊆ K.edgeSet ∧ P K ∧
      (∀ J : SimpleGraph V, K.edgeSet ⊆ J.edgeSet → P J →
        J.edgeSet ⊆ K.edgeSet) := by sorry
