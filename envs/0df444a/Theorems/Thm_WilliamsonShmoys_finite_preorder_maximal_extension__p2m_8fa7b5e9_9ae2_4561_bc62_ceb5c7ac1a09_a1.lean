-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_preorder_maximal_extension__p2m_8fa7b5e9_9ae2_4561_bc62_ceb5c7ac1a09_a1
-- name    : WilliamsonShmoys.finite_preorder_maximal_extension__p2m_8fa7b5e9_9ae2_4561_bc62_ceb5c7ac1a09_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:40:27.819191+00:00
-- url     : https://prove2.me/theorems/82cb2187-01bc-45f1-9c62-6084064a6bea
-- title:
--   Maximal extension in a finite partial order
-- statement:
--   In a finite partially ordered type, if a predicate holds at an element x, there is an element y above x satisfying the predicate that is maximal among predicate-satisfying elements above x.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_preorder_maximal_extension__p2m_8fa7b5e9_9ae2_4561_bc62_ceb5c7ac1a09_a1
    {α : Type} [Finite α] [PartialOrder α]
    (P : α → Prop) (x : α) (hx : P x) :
    Exists fun y : α => And (x ≤ y) (And (P y)
      (forall z : α, y ≤ z → P z → z ≤ y)) := by sorry
