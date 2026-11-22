-- Prove2me | Theorems.Thm_markov_abs
-- name    : markov_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:38:43.25604+00:00
-- url     : https://prove2.me/theorems/ff117150-0e62-4dee-823e-351e466b7e9a
-- title:
--   markov abs: markov abs
-- statement:
--   Markov's inequality with absolute values.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/DiscreteProbability.lean#L43-L46
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/DiscreteProbability.lean#L43-L46

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_Polychromatic_DiscreteProbability
set_option autoImplicit true
open Finset
variable {ι α : Type*} {s : Finset ι} {p f : ι → α} {c : α} [LinearOrder α]

theorem markov_abs [DivisionRing α] [IsStrictOrderedRing α]
    (hp : ∀ i ∈ s, 0 ≤ p i) (hc : 0 < c) :
    ∑ i ∈ s with c ≤ |f i|, p i ≤ (∑ i ∈ s, p i * |f i|) / c := by sorry
