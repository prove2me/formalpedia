-- Prove2me | Theorems.Thm_finite_set_exists_maximal__p2m_0d714fcf_7da8_48c8_afc4_fedf819778b0_a2
-- name    : finite_set_exists_maximal__p2m_0d714fcf_7da8_48c8_afc4_fedf819778b0_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:46:09.649976+00:00
-- url     : https://prove2.me/theorems/d3d7bbf4-5185-4589-badf-1f2afdcbd8c4
-- title:
--   A nonempty finite subset of a preorder has a maximal element
-- statement:
--   Every nonempty finite subset of a preorder contains an element such that any member above it is also below it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_set_exists_maximal__p2m_0d714fcf_7da8_48c8_afc4_fedf819778b0_a2
    {α : Type} [Preorder α] [Finite α]
    (s : Set α) (hs : s.Finite) (hne : s.Nonempty) :
    ∃ a ∈ s, ∀ b ∈ s, a ≤ b → b ≤ a := by sorry
