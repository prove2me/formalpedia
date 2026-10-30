-- Prove2me | Theorems.Thm_exists_maximal_of_nonempty_finset__p2m_5ce86dee_a51b_43d9_9c16_6a53f5f31031_a3
-- name    : exists_maximal_of_nonempty_finset__p2m_5ce86dee_a51b_43d9_9c16_6a53f5f31031_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:18:26.608801+00:00
-- url     : https://prove2.me/theorems/5643a87f-8c49-45e7-9188-71b2aafb1716
-- title:
--   A nonempty finite subset of a partial order has a maximal element
-- statement:
--   Every nonempty finite subset of a partial order contains a maximal element. The parent applies this to the finite set of graphs extending H and satisfying P. An independent proof chooses an element with a largest upper cone within the set; a strict extension would have a strictly smaller upper cone.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem exists_maximal_of_nonempty_finset__p2m_5ce86dee_a51b_43d9_9c16_6a53f5f31031_a3
    {α : Type} [PartialOrder α] (s : Finset α) (hs : s.Nonempty) :
    ∃ x ∈ s, ∀ y ∈ s, x ≤ y → y ≤ x := by
  sorry
