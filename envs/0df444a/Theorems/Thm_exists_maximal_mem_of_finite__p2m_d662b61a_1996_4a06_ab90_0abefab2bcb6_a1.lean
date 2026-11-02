-- Prove2me | Theorems.Thm_exists_maximal_mem_of_finite__p2m_d662b61a_1996_4a06_ab90_0abefab2bcb6_a1
-- name    : exists_maximal_mem_of_finite__p2m_d662b61a_1996_4a06_ab90_0abefab2bcb6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:23:35.684198+00:00
-- url     : https://prove2.me/theorems/dee8291c-1536-479f-83cf-d5565c1e2319
-- title:
--   Maximal element in a nonempty subset of a finite partial order
-- statement:
--   Every nonempty subset of a finite partially ordered type contains an element with no strictly larger member in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_maximal_mem_of_finite__p2m_d662b61a_1996_4a06_ab90_0abefab2bcb6_a1
    {α : Type} [Finite α] [PartialOrder α] (S : Set α) (hS : S.Nonempty) :
    ∃ a ∈ S, ∀ b ∈ S, a ≤ b → b = a := by
  sorry
