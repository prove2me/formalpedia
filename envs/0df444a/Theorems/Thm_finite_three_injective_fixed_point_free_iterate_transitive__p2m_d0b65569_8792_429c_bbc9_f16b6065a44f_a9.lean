-- Prove2me | Theorems.Thm_finite_three_injective_fixed_point_free_iterate_transitive__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a9
-- name    : finite_three_injective_fixed_point_free_iterate_transitive__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a9
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:28:05.388057+00:00
-- url     : https://prove2.me/theorems/11260284-6e2e-423c-b6a9-dbba656071b8
-- title:
--   An invariant three-element fiber is one successor orbit
-- statement:
--   Restrict `f` to the subtype defined by `P`. The preservation and injectivity hypotheses make the restriction an injective self-map of a three-element finite type, while `hfixed` excludes fixed points. This removes the finite orbit argument from the parent. A direct proof shows the first three iterates from any point are distinct, hence exhaust the subtype, then transfers the resulting iterate back to `α`. The remaining core obligation is this finite argument; the stated cardinality and all three map hypotheses are needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_three_injective_fixed_point_free_iterate_transitive__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a9
    {α : Type} [Fintype α] (f : α → α) (P : α → Prop) [DecidablePred P]
    (hcard : Fintype.card {x : α // P x} = 3)
    (hpres : ∀ x, P x → P (f x))
    (hinj : Function.Injective f) (hfixed : ∀ x, Not (f x = x)) :
    ∀ x y : α, P x → P y → ∃ k : Nat, f^[k] x = y := by sorry
