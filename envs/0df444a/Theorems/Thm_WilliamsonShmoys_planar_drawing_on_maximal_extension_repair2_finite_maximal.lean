-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_on_maximal_extension_repair2_finite_maximal
-- name    : WilliamsonShmoys.planar_drawing_on_maximal_extension_repair2_finite_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:37:27.154218+00:00
-- url     : https://prove2.me/theorems/45fb5931-03c7-43c1-8a9f-7e34ce98663a
-- title:
--   Maximal element of a finite subset of a partial order
-- statement:
--   Every nonempty finite subset of a partial order contains an element maximal within that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_on_maximal_extension_repair2_finite_maximal
    {α : Type} [PartialOrder α]
    (s : Set α) (hne : s.Nonempty) (hfin : s.Finite) :
    ∃ a ∈ s, ∀ b ∈ s, a ≤ b → b ≤ a := by
  sorry
