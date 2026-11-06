-- Prove2me | Theorems.Thm_finite_three_injective_fixed_point_free_iterate_transitive__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6
-- name    : finite_three_injective_fixed_point_free_iterate_transitive__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T20:57:54.604+00:00
-- url     : https://prove2.me/theorems/c087dd6c-81e7-4e4c-ad72-7053d1a189f4
-- title:
--   An invariant three-element fiber is one successor orbit
-- statement:
--   Restrict the function to the invariant subtype. Injectivity and finiteness make that restriction a permutation; on three elements, a permutation with no fixed points has a single orbit of length three. This isolates the finite-permutation argument used by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_three_injective_fixed_point_free_iterate_transitive__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6
    {α : Type} [Fintype α] (f : α -> α) (P : α -> Prop) [DecidablePred P]
    (hcard : Fintype.card {x : α // P x} = 3)
    (hpres : forall x, P x -> P (f x))
    (hinj : Function.Injective f) (hfixed : forall x, f x ≠ x) :
    forall x y : α, P x -> P y -> exists k : Nat, f^[k] x = y := by
  sorry
