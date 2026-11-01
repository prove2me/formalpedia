-- Prove2me | Theorems.Thm_finite_three_injective_fixed_point_free_iterate_transitive_aux__p2m_c087dd6c_81e7_4e4c_ad72_7053d1a189f4_a1
-- name    : finite_three_injective_fixed_point_free_iterate_transitive_aux__p2m_c087dd6c_81e7_4e4c_ad72_7053d1a189f4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:09:56.213129+00:00
-- url     : https://prove2.me/theorems/e34ab9fc-b523-4695-9fb3-ea04f86c1c1c
-- title:
--   A fixed-point-free injection on three elements is transitive
-- statement:
--   For a finite type with exactly three elements, every injective self-map with no fixed points has iterates connecting every ordered pair.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_three_injective_fixed_point_free_iterate_transitive_aux__p2m_c087dd6c_81e7_4e4c_ad72_7053d1a189f4_a1
    {α : Type} [Fintype α] (f : α → α)
    (hcard : Fintype.card α = 3)
    (hinj : Function.Injective f) (hfixed : ∀ x, f x ≠ x) :
    ∀ x y : α, ∃ k : Nat, f^[k] x = y := by
  sorry
