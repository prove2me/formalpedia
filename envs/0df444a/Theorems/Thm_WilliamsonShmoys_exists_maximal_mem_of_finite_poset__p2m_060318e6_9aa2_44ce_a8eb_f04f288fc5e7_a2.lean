-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_mem_of_finite_poset__p2m_060318e6_9aa2_44ce_a8eb_f04f288fc5e7_a2
-- name    : WilliamsonShmoys.exists_maximal_mem_of_finite_poset__p2m_060318e6_9aa2_44ce_a8eb_f04f288fc5e7_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:39:24.047206+00:00
-- url     : https://prove2.me/theorems/74926f1b-cf65-47ca-8ae8-fb53b0023112
-- title:
--   A nonempty finite subset of a partial order has a maximal element
-- statement:
--   Every nonempty finite subset of a partial order contains an element that is maximal within that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_mem_of_finite_poset__p2m_060318e6_9aa2_44ce_a8eb_f04f288fc5e7_a2
    {α : Type} [Fintype α] [PartialOrder α]
    (s : Finset α) (hs : s.Nonempty) :
    ∃ a ∈ s, ∀ b ∈ s, a ≤ b → b ≤ a := by sorry
