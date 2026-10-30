-- Prove2me | Theorems.Thm_finite_extension_maximal_by_measure__p2m_a06e74bc_2d14_4a85_b8d6_42f2136549b3_a1
-- name    : finite_extension_maximal_by_measure__p2m_a06e74bc_2d14_4a85_b8d6_42f2136549b3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:31:51.974791+00:00
-- url     : https://prove2.me/theorems/fafb23b8-884f-4b1e-a536-dfeeeba0ad93
-- title:
--   Finite extensions have a maximal measured element
-- statement:
--   In a finite type, if R is reflexive and transitive and every distinct R-extension strictly increases a natural-number measure, every P-element has a P-extension that is maximal among P-elements.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem finite_extension_maximal_by_measure__p2m_a06e74bc_2d14_4a85_b8d6_42f2136549b3_a1
    {α : Type} [Fintype α]
    (R : α → α → Prop)
    (measure : α → Nat)
    (P : α → Prop)
    (hrefl : ∀ a, R a a)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hstrict : ∀ a b, R a b → a ≠ b → measure a < measure b)
    (x : α) (hx : P x) :
    ∃ y, R x y ∧ P y ∧ ∀ z, R y z → P z → z = y := by sorry
