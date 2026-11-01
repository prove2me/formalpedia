-- Prove2me | Theorems.Thm_finite_partialOrder_has_maximal_for_predicate__p2m_a870ea81_7152_406d_9ca9_18eedb61291e_a1
-- name    : finite_partialOrder_has_maximal_for_predicate__p2m_a870ea81_7152_406d_9ca9_18eedb61291e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:26:16.617199+00:00
-- url     : https://prove2.me/theorems/f0d16d19-0481-4810-a594-0144d0b4e69f
-- title:
--   A nonempty predicate on a finite partial order has a maximal element
-- statement:
--   Every nonempty subset of a finite partial order has an element with no distinct larger element in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem finite_partialOrder_has_maximal_for_predicate__p2m_a870ea81_7152_406d_9ca9_18eedb61291e_a1
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) [DecidablePred P] (hne : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → a ≤ b → b = a := by
  sorry
