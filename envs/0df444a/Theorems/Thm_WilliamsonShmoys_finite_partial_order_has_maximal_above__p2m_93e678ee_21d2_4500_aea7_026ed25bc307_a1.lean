-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_partial_order_has_maximal_above__p2m_93e678ee_21d2_4500_aea7_026ed25bc307_a1
-- name    : WilliamsonShmoys.finite_partial_order_has_maximal_above__p2m_93e678ee_21d2_4500_aea7_026ed25bc307_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:42:29.208015+00:00
-- url     : https://prove2.me/theorems/83ad1936-fd92-4209-9abb-f0c3d7c626d9
-- title:
--   A finite partial order has a maximal element above each element
-- statement:
--   In a finite type with a reflexive, transitive, antisymmetric relation, every element lies below a maximal element. For the target, the type consists of planar graphs containing M and the relation is adjacency inclusion. This removes the finite maximal-selection step from the parent; prove it by taking a maximal element in the finite set of elements related above a. The parent then checks that planar supergraphs of the chosen graph remain in that type, using transitivity of adjacency inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_partial_order_has_maximal_above__p2m_93e678ee_21d2_4500_aea7_026ed25bc307_a1
    {α : Type} [Fintype α] (r : α → α → Prop)
    (hrefl : ∀ a, r a a)
    (htrans : ∀ a b c, r a b → r b c → r a c)
    (hantisymm : ∀ a b, r a b → r b a → a = b)
    (a : α) :
    ∃ b, r a b ∧ ∀ c, r b c → c = b := by sorry
