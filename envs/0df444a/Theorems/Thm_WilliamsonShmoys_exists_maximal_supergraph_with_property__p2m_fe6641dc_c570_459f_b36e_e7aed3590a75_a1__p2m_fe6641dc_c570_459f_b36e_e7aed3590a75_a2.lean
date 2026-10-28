-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_with_property__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a1__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a2
-- name    : WilliamsonShmoys.exists_maximal_supergraph_with_property__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a1__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:32:07.644246+00:00
-- url     : https://prove2.me/theorems/9ded64de-7a59-4a66-875b-3c7a1e0e31cc
-- title:
--   Finite maximal supergraph for a downward-closed graph property
-- statement:
--   For a finite ordered vertex type, any graph satisfying a property preserved under edge removal has a supergraph with that property whose edge set is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_with_property__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a1__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (Q : SimpleGraph V → Prop)
    (hK : Q K)
    (hdown : ∀ {G H : SimpleGraph V}, H.edgeSet ⊆ G.edgeSet → Q G → Q H) :
    ∃ P : SimpleGraph V,
      K.edgeSet ⊆ P.edgeSet ∧
      Q P ∧
      ∀ L : SimpleGraph V,
        P.edgeSet ⊆ L.edgeSet →
        Q L →
        L.edgeSet ⊆ P.edgeSet := by sorry
