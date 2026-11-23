-- Prove2me | Theorems.Thm_span_ne_mem_kaplanskiSet
-- name    : span_ne_mem_kaplanskiSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:13:21.437405+00:00
-- url     : https://prove2.me/theorems/261e2e2b-ac4a-4f5a-b773-a1b433d90ecb
-- title:
--   span ne mem kaplanski Set: span ne mem kaplanski Set
-- statement:
--   The span ne mem kaplanski Set construction uses the span ne mem kaplanski Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/riccardobrasca/kaplanski4/blob/0989e6dc65081ab46709aac8a204a65f58ff52ee/Kaplanski4/Kaplanski.lean#L44-L56
-- source:
--   https://github.com/riccardobrasca/kaplanski4/blob/0989e6dc65081ab46709aac8a204a65f58ff52ee/Kaplanski4/Kaplanski.lean#L44-L56

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import Mathlib.RingTheory.PowerSeries.Ideal
import Definitions.Def_Kaplanski4_Kaplanski
set_option autoImplicit false
variable {R : Type*}
open Set Ideal Submonoid
variable [CommSemiring R] [IsDomain R]

theorem span_ne_mem_kaplanskiSet {a : R} (ha : a ≠ 0)
      (H : ∀ I ≠ (⊥ : Ideal R), I.IsPrime → ∃ x ∈ I, Prime x) :
    span {a} ∉ kaplanskySet (closure {r : R | Prime r}).toSubsemigroup := by sorry
