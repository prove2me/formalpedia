-- Prove2me | Theorems.Thm_uniqueFactorizationMonoid_of_exists_prime
-- name    : uniqueFactorizationMonoid_of_exists_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:13:19.967929+00:00
-- url     : https://prove2.me/theorems/2f22d511-e607-4f0e-8445-2cb6406c516b
-- title:
--   unique Factorization Monoid of exists prime: unique Factorization Monoid of exists prime
-- statement:
--   The other implication of Kaplansky's criterion (if every nonzero prime ideal of
--   an integral domain R contains a prime element, then R is a UFD).
--
--   Source: https://github.com/riccardobrasca/kaplanski4/blob/0989e6dc65081ab46709aac8a204a65f58ff52ee/Kaplanski4/Kaplanski.lean#L60-L83
-- source:
--   https://github.com/riccardobrasca/kaplanski4/blob/0989e6dc65081ab46709aac8a204a65f58ff52ee/Kaplanski4/Kaplanski.lean#L60-L83

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import Mathlib.RingTheory.PowerSeries.Ideal
import Definitions.Def_Kaplanski4_Kaplanski
set_option autoImplicit false
variable {R : Type*}
open Set Ideal Submonoid
variable [CommSemiring R] [IsDomain R]

theorem uniqueFactorizationMonoid_of_exists_prime
    (H : ∀ I ≠ (⊥ : Ideal R), I.IsPrime → ∃ x ∈ I, Prime x) : UniqueFactorizationMonoid R := by sorry
