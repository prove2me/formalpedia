-- Prove2me | Theorems.Thm_finite_three_injective_fixed_point_free_iterate_transitive__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a5
-- name    : finite_three_injective_fixed_point_free_iterate_transitive__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:46:34.466148+00:00
-- url     : https://prove2.me/theorems/d6d77b5a-b316-44d0-92b6-f8990fc8278c
-- title:
--   An invariant three-element fiber is one successor orbit
-- statement:
--   Restrict `f` to the invariant subtype. Injectivity on this finite three-element type makes the restriction a permutation. Its cycles have lengths dividing three, and the no-fixed-point assumption excludes length one, so each orbit contains every subtype element. This isolates the finite-permutation argument needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_three_injective_fixed_point_free_iterate_transitive__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a5
    {α : Type} [Fintype α] (f : α → α) (P : α → Prop) [DecidablePred P]
    (hcard : Fintype.card {x : α // P x} = 3)
    (hpres : ∀ x, P x → P (f x))
    (hinj : Function.Injective f) (hfixed : ∀ x, f x ≠ x) :
    ∀ x y : α, P x → P y → ∃ k : Nat, f^[k] x = y := by
  sorry
