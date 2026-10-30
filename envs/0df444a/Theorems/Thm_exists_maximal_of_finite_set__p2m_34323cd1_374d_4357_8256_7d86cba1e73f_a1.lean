-- Prove2me | Theorems.Thm_exists_maximal_of_finite_set__p2m_34323cd1_374d_4357_8256_7d86cba1e73f_a1
-- name    : exists_maximal_of_finite_set__p2m_34323cd1_374d_4357_8256_7d86cba1e73f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:05:43.58398+00:00
-- url     : https://prove2.me/theorems/48e7e4be-1e78-4222-ad43-353cad6867a9
-- title:
--   Maximal element of a nonempty finite partially ordered set
-- statement:
--   Every nonempty finite subset of a partial order contains an element with no strictly greater element in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_maximal_of_finite_set__p2m_34323cd1_374d_4357_8256_7d86cba1e73f_a1 {α : Type} [PartialOrder α] (S : Set α) (hS : S.Finite) (hSne : S.Nonempty) : ∃ a ∈ S, ∀ b ∈ S, a ≤ b → b = a := by sorry
