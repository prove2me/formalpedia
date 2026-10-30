-- Prove2me | Theorems.Thm_fintype_card_two_elim__p2m_551112cf_8b4c_4517_8603_726684976d71_a4
-- name    : fintype_card_two_elim__p2m_551112cf_8b4c_4517_8603_726684976d71_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:29:38.148293+00:00
-- url     : https://prove2.me/theorems/335388ed-8b9f-4a64-a44a-05bce76fac29
-- title:
--   A two-element finite type is exhausted by any two distinct elements
-- statement:
--   If a finite type has cardinality two, any two distinct elements exhaust it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem fintype_card_two_elim__p2m_551112cf_8b4c_4517_8603_726684976d71_a4
    {α : Type} [Fintype α]
    (hcard : Fintype.card α = 2)
    (x y : α)
    (hxy : x ≠ y) :
    ∀ z : α, z = x ∨ z = y := by sorry
