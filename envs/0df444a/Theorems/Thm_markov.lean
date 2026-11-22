-- Prove2me | Theorems.Thm_markov
-- name    : markov
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:34:34.116461+00:00
-- url     : https://prove2.me/theorems/1422679e-5ef6-443a-a684-d12e90d49df4
-- title:
--   markov: markov
-- statement:
--   Markov's inequality for weighted sums: the total weight of elements exceeding threshold `c`
--   is at most the weighted average divided by `c`.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/DiscreteProbability.lean#L30-L40
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/DiscreteProbability.lean#L30-L40

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_Polychromatic_DiscreteProbability
set_option autoImplicit true
open Finset
variable {ι α : Type*} {s : Finset ι} {p f : ι → α} {c : α} [LinearOrder α]

theorem markov [DivisionSemiring α] [IsStrictOrderedRing α]
    (hp : ∀ i ∈ s, 0 ≤ p i) (hf : ∀ i ∈ s, 0 ≤ f i) (hc : 0 < c) :
    ∑ i ∈ s with c ≤ f i, p i ≤ (∑ i ∈ s, p i * f i) / c := by sorry
