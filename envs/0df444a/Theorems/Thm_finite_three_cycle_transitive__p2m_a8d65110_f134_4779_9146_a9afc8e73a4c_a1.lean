-- Prove2me | Theorems.Thm_finite_three_cycle_transitive__p2m_a8d65110_f134_4779_9146_a9afc8e73a4c_a1
-- name    : finite_three_cycle_transitive__p2m_a8d65110_f134_4779_9146_a9afc8e73a4c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:21:36.91036+00:00
-- url     : https://prove2.me/theorems/b4c44d04-edb9-41a7-ac17-6db35041007a
-- title:
--   A fixed-point-free injective map on three elements is transitive under iteration
-- statement:
--   For a finite type with exactly three elements, an injective self-map with no fixed points has a single orbit: every element is an iterate of every starting element. The boundary case is handled by the hypotheses themselves: fixed-point-freeness rules out an orbit of length one, and injectivity rules out a two-element cycle, leaving the three distinct points x, g x, and g (g x), which exhaust the type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_three_cycle_transitive__p2m_a8d65110_f134_4779_9146_a9afc8e73a4c_a1
    {α : Type} [Fintype α] (g : α → α)
    (hcard : Fintype.card α = 3)
    (hinj : Function.Injective g)
    (hfixed : ∀ x, g x ≠ x) :
    ∀ x y : α, ∃ k : Nat, g^[k] x = y := by sorry
