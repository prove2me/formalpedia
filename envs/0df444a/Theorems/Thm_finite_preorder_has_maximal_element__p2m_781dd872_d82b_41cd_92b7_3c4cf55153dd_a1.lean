-- Prove2me | Theorems.Thm_finite_preorder_has_maximal_element__p2m_781dd872_d82b_41cd_92b7_3c4cf55153dd_a1
-- name    : finite_preorder_has_maximal_element__p2m_781dd872_d82b_41cd_92b7_3c4cf55153dd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:20:51.727993+00:00
-- url     : https://prove2.me/theorems/3bd22180-02ea-4316-a15e-0c9501c3cce4
-- title:
--   A nonempty subset of a finite preorder has a maximal element
-- statement:
--   Every nonempty subset of a finite preorder contains an element maximal within that subset, where maximality means that every larger member is also below it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_preorder_has_maximal_element__p2m_781dd872_d82b_41cd_92b7_3c4cf55153dd_a1
    {α : Type} [Finite α] [Preorder α]
    (S : Set α) (hS : S.Nonempty) :
    ∃ a ∈ S, ∀ b, a ≤ b → b ∈ S → b ≤ a := by sorry
