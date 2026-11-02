-- Prove2me | Theorems.Thm_exists_maximal_element_finite__p2m_8824e35c_b427_4577_adf2_2966f46879ec_a1
-- name    : exists_maximal_element_finite__p2m_8824e35c_b427_4577_adf2_2966f46879ec_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:15:55.652751+00:00
-- url     : https://prove2.me/theorems/d09dd93f-c69e-42eb-bee3-d59d61fb1cc8
-- title:
--   A nonempty finite partial order has a maximal element
-- statement:
--   Every nonempty predicate on a finite partial order contains an element with no strictly larger element in that predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_maximal_element_finite__p2m_8824e35c_b427_4577_adf2_2966f46879ec_a1
    {α : Type} [Fintype α] [PartialOrder α] (p : α → Prop)
    (hne : ∃ a, p a) :
    ∃ a, p a ∧ ∀ b, p b → a ≤ b → b = a := by sorry
