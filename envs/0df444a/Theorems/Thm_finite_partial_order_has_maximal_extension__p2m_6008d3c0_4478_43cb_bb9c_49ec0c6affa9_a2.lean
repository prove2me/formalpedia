-- Prove2me | Theorems.Thm_finite_partial_order_has_maximal_extension__p2m_6008d3c0_4478_43cb_bb9c_49ec0c6affa9_a2
-- name    : finite_partial_order_has_maximal_extension__p2m_6008d3c0_4478_43cb_bb9c_49ec0c6affa9_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:51:28.482579+00:00
-- url     : https://prove2.me/theorems/53f6a479-f4c7-41e7-b49a-fcb2d3dd7708
-- title:
--   Maximal extension in a finite partial order
-- statement:
--   Every element of a finite partially ordered type lies below a maximal element.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem finite_partial_order_has_maximal_extension__p2m_6008d3c0_4478_43cb_bb9c_49ec0c6affa9_a2
    {α : Type} [Finite α] [PartialOrder α] (a : α) :
    ∃ b : α, a ≤ b ∧ ∀ c : α, b ≤ c → c = b := by sorry
