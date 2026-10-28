-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_element_of_finite_set_planar_extension_20261026
-- name    : WilliamsonShmoys.exists_maximal_element_of_finite_set_planar_extension_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:57:20.080376+00:00
-- url     : https://prove2.me/theorems/f0f0a410-bd31-4c20-9396-da695ce07578
-- title:
--   A nonempty subset of a finite partial order has a maximal element
-- statement:
--   Every nonempty subset of a finite partial order has an element with no strictly larger element in that subset. This yields the maximal planar supergraph once applied to the set of planar supergraphs containing K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximal_element_of_finite_set_planar_extension_20261026 {α : Type} [PartialOrder α] [Finite α] (S : Set α) (hS : S.Nonempty) : ∃ a, a ∈ S ∧ ∀ b, a ≤ b → b ∈ S → b = a := by sorry
