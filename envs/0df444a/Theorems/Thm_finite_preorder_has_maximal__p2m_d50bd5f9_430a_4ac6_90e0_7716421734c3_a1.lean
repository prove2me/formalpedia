-- Prove2me | Theorems.Thm_finite_preorder_has_maximal__p2m_d50bd5f9_430a_4ac6_90e0_7716421734c3_a1
-- name    : finite_preorder_has_maximal__p2m_d50bd5f9_430a_4ac6_90e0_7716421734c3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:46:10.719711+00:00
-- url     : https://prove2.me/theorems/53dcddd8-054c-4e6b-b164-19088b161fd0
-- title:
--   Maximal element in a finite preorder subset
-- statement:
--   Every nonempty predicate-defined subset of a finite preorder contains an element with no strictly larger member in that subset: whenever the chosen element is below another member, that other member is also below the chosen one.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_preorder_has_maximal__p2m_d50bd5f9_430a_4ac6_90e0_7716421734c3_a1
    {α : Type} [Preorder α] [Finite α]
    (P : α → Prop) (hne : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → x ≤ y → y ≤ x := by sorry
