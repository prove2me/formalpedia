-- Prove2me | Theorems.Thm_uniqueFactorizationMonoid_iff
-- name    : uniqueFactorizationMonoid_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:13:25.457984+00:00
-- url     : https://prove2.me/theorems/0ee8d1ab-0745-405a-bf0c-8d7185b80eb2
-- title:
--   unique Factorization Monoid iff: unique Factorization Monoid iff
-- statement:
--   Kaplansky's criterion (an integral domain R is a UFD if and only if every nonzero prime ideal
--   contains a prime element).
--
--   Source: https://github.com/riccardobrasca/kaplanski4/blob/0989e6dc65081ab46709aac8a204a65f58ff52ee/Kaplanski4/Kaplanski.lean#L87-L90
-- source:
--   https://github.com/riccardobrasca/kaplanski4/blob/0989e6dc65081ab46709aac8a204a65f58ff52ee/Kaplanski4/Kaplanski.lean#L87-L90

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import Mathlib.RingTheory.PowerSeries.Ideal
import Definitions.Def_Kaplanski4_Kaplanski
set_option autoImplicit false
variable {R : Type*}
open Set Ideal Submonoid
variable [CommSemiring R] [IsDomain R]

theorem uniqueFactorizationMonoid_iff :
    UniqueFactorizationMonoid R ↔ ∀ I ≠ (⊥ : Ideal R), I.IsPrime → ∃ x ∈ I, Prime x := by sorry
