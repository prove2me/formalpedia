-- Prove2me | Theorems.Thm_finite_family_maximum__p2m_4d05bb9d_42a1_4f6c_b6b4_be7b1a8f6d1e_a1
-- name    : finite_family_maximum__p2m_4d05bb9d_42a1_4f6c_b6b4_be7b1a8f6d1e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:36:25.435208+00:00
-- url     : https://prove2.me/theorems/d38bd3f7-0e69-4a41-ad46-7ea65606e820
-- title:
--   Maximum of a predicate on a finite type
-- statement:
--   For a nonempty predicate on a finite type, some satisfying element maximizes any natural-valued measure.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem finite_family_maximum__p2m_4d05bb9d_42a1_4f6c_b6b4_be7b1a8f6d1e_a1
    {α : Type} [Fintype α] (P : α → Prop) (measure : α → Nat)
    (hex : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → measure b ≤ measure a := by sorry
