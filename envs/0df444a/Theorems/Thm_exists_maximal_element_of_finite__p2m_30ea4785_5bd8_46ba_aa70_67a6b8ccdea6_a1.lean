-- Prove2me | Theorems.Thm_exists_maximal_element_of_finite__p2m_30ea4785_5bd8_46ba_aa70_67a6b8ccdea6_a1
-- name    : exists_maximal_element_of_finite__p2m_30ea4785_5bd8_46ba_aa70_67a6b8ccdea6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:42:06.589597+00:00
-- url     : https://prove2.me/theorems/4e9d1b27-2a93-4e5a-9fab-7e107ae1d946
-- title:
--   A nonempty upward cone in a finite partial order has a maximal member
-- statement:
--   For any predicate on a finite partially ordered type, if it holds at `a`, then some element satisfying it and lying above `a` is maximal among such elements.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_maximal_element_of_finite__p2m_30ea4785_5bd8_46ba_aa70_67a6b8ccdea6_a1
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) (a : α) (ha : P a) :
    ∃ m : α, P m ∧ a ≤ m ∧ ∀ k : α, m ≤ k → P k → k = m := by
  sorry
