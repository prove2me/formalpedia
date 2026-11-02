-- Prove2me | Theorems.Thm_finite_exists_max_rank__p2m_9e5fb9d2_aa0e_41c4_9a80_cb078400c4e8_a1
-- name    : finite_exists_max_rank__p2m_9e5fb9d2_aa0e_41c4_9a80_cb078400c4e8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:48:16.32396+00:00
-- url     : https://prove2.me/theorems/bdf97719-7e69-4f0d-9af9-61697ad7acb0
-- title:
--   Maximum rank in a finite nonempty feasible family
-- statement:
--   On a finite type, any nonempty feasible family has an element whose natural-number rank is at least the rank of every feasible element. This is a generic finite maximization lemma, provable by enumerating the type and taking a maximum over the feasible elements.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_exists_max_rank__p2m_9e5fb9d2_aa0e_41c4_9a80_cb078400c4e8_a1 {α : Type} [Finite α] (P : α → Prop) (rank : α → Nat) (hex : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → rank b ≤ rank a := by sorry
