-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_mem_finite_set
-- name    : WilliamsonShmoys.exists_maximal_mem_finite_set
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:53:57.446603+00:00
-- url     : https://prove2.me/theorems/8137c281-2e93-4dda-acbf-c839a1615906
-- title:
--   Maximal element in a nonempty finite preorder subset
-- statement:
--   A nonempty finite subset of a preorder contains an element with no strict extension inside the subset, expressed by requiring every larger member to be below it as well. Applied to drawable supergraphs, this yields equality for any drawable extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_mem_finite_set
    {α : Type} [Preorder α] (s : Set α) (hs : s.Finite)
    (hne : s.Nonempty) :
    ∃ a, a ∈ s ∧ ∀ b, b ∈ s → a ≤ b → b ≤ a := by sorry
