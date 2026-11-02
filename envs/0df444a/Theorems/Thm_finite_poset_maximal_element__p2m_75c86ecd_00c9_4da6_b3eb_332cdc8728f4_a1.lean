-- Prove2me | Theorems.Thm_finite_poset_maximal_element__p2m_75c86ecd_00c9_4da6_b3eb_332cdc8728f4_a1
-- name    : finite_poset_maximal_element__p2m_75c86ecd_00c9_4da6_b3eb_332cdc8728f4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:51:35.345196+00:00
-- url     : https://prove2.me/theorems/e50421bf-a1be-4e01-88bc-984ea95e2843
-- title:
--   Maximal element above a predicate-satisfying element in a finite poset
-- statement:
--   In a finite partially ordered type, any element satisfying a predicate lies below a predicate-satisfying element that is maximal among predicate-satisfying elements above it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_poset_maximal_element__p2m_75c86ecd_00c9_4da6_b3eb_332cdc8728f4_a1
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) (a : α) (ha : P a) :
    ∃ t : α, a ≤ t ∧ P t ∧
      ∀ u : α, t ≤ u → P u → u = t := by sorry
