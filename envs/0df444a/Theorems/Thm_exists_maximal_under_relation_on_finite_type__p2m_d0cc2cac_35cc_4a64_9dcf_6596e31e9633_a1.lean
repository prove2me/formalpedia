-- Prove2me | Theorems.Thm_exists_maximal_under_relation_on_finite_type__p2m_d0cc2cac_35cc_4a64_9dcf_6596e31e9633_a1
-- name    : exists_maximal_under_relation_on_finite_type__p2m_d0cc2cac_35cc_4a64_9dcf_6596e31e9633_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:33:54.269225+00:00
-- url     : https://prove2.me/theorems/9d164158-4cb6-4ed5-abe0-4a5533e5fe3a
-- title:
--   Maximal element in a nonempty subset of a finite partial order
-- statement:
--   In a finite type with a reflexive, transitive, antisymmetric relation, every nonempty subset contains an element with no strictly greater element in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_maximal_under_relation_on_finite_type__p2m_d0cc2cac_35cc_4a64_9dcf_6596e31e9633_a1
    {α : Type} [Fintype α]
    (R : α → α → Prop)
    (hRrefl : ∀ x, R x x)
    (hRtrans : ∀ x y z, R x y → R y z → R x z)
    (hRantisymm : ∀ x y, R x y → R y x → x = y)
    (S : α → Prop)
    (hS : ∃ x, S x) :
    ∃ b, S b ∧ ∀ c, S c → R b c → R c b := by sorry
