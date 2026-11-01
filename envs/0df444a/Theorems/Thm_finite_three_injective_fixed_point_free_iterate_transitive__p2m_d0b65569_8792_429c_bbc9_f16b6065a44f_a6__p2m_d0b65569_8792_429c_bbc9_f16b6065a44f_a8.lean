-- Prove2me | Theorems.Thm_finite_three_injective_fixed_point_free_iterate_transitive__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a8
-- name    : finite_three_injective_fixed_point_free_iterate_transitive__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a8
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:17:15.077765+00:00
-- url     : https://prove2.me/theorems/a8d65110-f134-4779-9146-a9afc8e73a4c
-- title:
--   An invariant three-element fiber is one successor orbit
-- statement:
--   Restrict `f` to the invariant subtype defined by `P`. Injectivity makes this map a permutation of the three-element subtype, and `hfixed` excludes fixed points. Prove the finite claim by showing that a permutation of three elements without fixed points is a 3-cycle, then translate its orbit back to iterates of `f`. This is the remaining core finite-permutation argument; the cardinality, invariance, injectivity, and fixed-point hypotheses are all needed by the parent reduction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_three_injective_fixed_point_free_iterate_transitive__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a8
    {α : Type} [Fintype α] (f : α -> α) (P : α -> Prop) [DecidablePred P]
    (hcard : Fintype.card {x : α // P x} = 3)
    (hpres : forall x, P x -> P (f x))
    (hinj : Function.Injective f) (hfixed : forall x, Not (f x = x)) :
    forall x y : α, P x -> P y -> exists k : Nat, f^[k] x = y := by sorry
