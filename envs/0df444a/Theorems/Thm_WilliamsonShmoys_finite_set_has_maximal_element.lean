-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_set_has_maximal_element
-- name    : WilliamsonShmoys.finite_set_has_maximal_element
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:22:12.879566+00:00
-- url     : https://prove2.me/theorems/e1cafaa4-4318-4a41-a7fb-5a4d77ef82f4
-- title:
--   Maximal element of a nonempty subset of a finite partial order
-- statement:
--   Every nonempty subset of a finite partially ordered type contains an element for which every larger member of the subset is equal to it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_set_has_maximal_element
    {alpha : Type} [Finite alpha] [PartialOrder alpha]
    (s : Set alpha) (hne : s.Nonempty) :
    Exists fun a : alpha => And (a ∈ s)
      (forall b : alpha, a <= b -> b ∈ s -> b = a) := by sorry
