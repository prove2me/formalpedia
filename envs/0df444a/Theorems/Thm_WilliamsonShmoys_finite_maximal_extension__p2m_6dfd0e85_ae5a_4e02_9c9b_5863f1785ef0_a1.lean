-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_6dfd0e85_ae5a_4e02_9c9b_5863f1785ef0_a1
-- name    : WilliamsonShmoys.finite_maximal_extension__p2m_6dfd0e85_ae5a_4e02_9c9b_5863f1785ef0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:50:48.203524+00:00
-- url     : https://prove2.me/theorems/6df50b67-5652-41c7-811c-0a800dad2e2b
-- title:
--   Finite maximal extension under a strictly increasing measure
-- statement:
--   In a finite type, if a reflexive and transitive relation strictly increases a natural-valued measure whenever related elements differ, every element satisfying a predicate has a predicate-satisfying related extension that is maximal among such extensions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_extension__p2m_6dfd0e85_ae5a_4e02_9c9b_5863f1785ef0_a1
    {α : Type} [Fintype α]
    (R : α → α → Prop) (μ : α → Nat) (P : α → Prop)
    (hrefl : ∀ x, R x x)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (hgrowth : ∀ x y, R x y → x ≠ y → μ x < μ y)
    (x : α) (hx : P x) :
    ∃ y, R x y ∧ P y ∧ ∀ z, R y z → P z → z = y := by sorry
