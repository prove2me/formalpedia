-- Prove2me | Theorems.Thm_exists_edge_maximal_property_extension__p2m_3d85fc57_8a7f_4a4a_b28a_c7b875c3ae9f_a1
-- name    : exists_edge_maximal_property_extension__p2m_3d85fc57_8a7f_4a4a_b28a_c7b875c3ae9f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:54:12.788718+00:00
-- url     : https://prove2.me/theorems/f4563021-e129-46b8-88e1-d6e2566dcdde
-- title:
--   Finite property-preserving extension has a maximal member
-- statement:
--   For a finite vertex type, every graph satisfying P has a P-preserving edge extension containing it that admits no further strict edge extension satisfying P.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_edge_maximal_property_extension__p2m_3d85fc57_8a7f_4a4a_b28a_c7b875c3ae9f_a1
    {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (H : SimpleGraph V)
    (hP : P H) :
    ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ P K ∧
      ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet → ¬ P L := by
  sorry
