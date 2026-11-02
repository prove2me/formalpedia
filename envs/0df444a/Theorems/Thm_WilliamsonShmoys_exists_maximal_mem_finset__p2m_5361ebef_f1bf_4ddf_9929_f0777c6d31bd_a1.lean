-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_mem_finset__p2m_5361ebef_f1bf_4ddf_9929_f0777c6d31bd_a1
-- name    : WilliamsonShmoys.exists_maximal_mem_finset__p2m_5361ebef_f1bf_4ddf_9929_f0777c6d31bd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:41:11.682238+00:00
-- url     : https://prove2.me/theorems/7b569995-c4c6-4850-b4cb-21f647ce021c
-- title:
--   A nonempty finite subset of a partial order has a maximal member
-- statement:
--   Every nonempty finite subset of a partial order contains an element that has no strictly larger member in that subset. Applied to the subset of graphs extending G and satisfying P, this gives the graph required by the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_mem_finset__p2m_5361ebef_f1bf_4ddf_9929_f0777c6d31bd_a1 {α : Type} [Fintype α] [PartialOrder α] (S : Finset α) (hS : S.Nonempty) : ∃ a ∈ S, ∀ b ∈ S, a ≤ b → b ≤ a := by sorry
