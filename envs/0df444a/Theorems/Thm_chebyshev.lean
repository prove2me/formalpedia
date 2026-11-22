-- Prove2me | Theorems.Thm_chebyshev
-- name    : chebyshev
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:38:51.06114+00:00
-- url     : https://prove2.me/theorems/d544b1a7-bbe3-4b0f-ad1a-023a96e66e32
-- title:
--   chebyshev: chebyshev
-- statement:
--   Chebyshev's inequality for weighted sums: the total weight of elements with
--   `|f i| ≥ c` is at most the weighted second moment divided by `c²`.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/DiscreteProbability.lean#L50-L54
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/DiscreteProbability.lean#L50-L54

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_Polychromatic_DiscreteProbability
set_option autoImplicit true
open Finset
variable {ι α : Type*} {s : Finset ι} {p f : ι → α} {c : α} [LinearOrder α]

theorem chebyshev [DivisionRing α] [IsStrictOrderedRing α]
    (hp : ∀ i ∈ s, 0 ≤ p i) (hc : 0 < c) :
    ∑ i ∈ s with c ≤ |f i|, p i ≤ (∑ i ∈ s, p i * f i ^ 2) / c ^ 2 := by sorry
