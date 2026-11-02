-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_preorder_has_maximal__p2m_7d28393b_3717_42d0_a7e1_00f1426861ad_a2
-- name    : WilliamsonShmoys.finite_preorder_has_maximal__p2m_7d28393b_3717_42d0_a7e1_00f1426861ad_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:04:37.053207+00:00
-- url     : https://prove2.me/theorems/f1d5cd47-35c1-4454-9f0d-b573cf6981e7
-- title:
--   A finite subset of a preorder has a maximal element
-- statement:
--   Every nonempty finite subset of a preorder has an element such that any element of the subset above it is also below it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_preorder_has_maximal__p2m_7d28393b_3717_42d0_a7e1_00f1426861ad_a2 {α : Type} [Fintype α] [Preorder α] (s : Finset α) (hne : s.Nonempty) : ∃ a : α, a ∈ s ∧ ∀ b : α, b ∈ s → a ≤ b → b ≤ a := by sorry
