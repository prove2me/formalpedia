-- Prove2me | Theorems.Thm_eVariationOn_add_le
-- name    : eVariationOn.add_le
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-10-04T22:34:45.971248+00:00
-- url     : https://prove2.me/theorems/75ba7b38-4264-42fc-b77f-9ea156d2ceb1
-- title:
--   Variation of a sum is at most the sum of variations
-- statement:
--   Subadditivity of variation.
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Topology/EMetricSpace/BoundedVariation.lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.Compact
open scoped BigOperators

namespace eVariationOn

theorem add_le {α E : Type*} [LinearOrder α]
    [SeminormedAddCommGroup E] (f g : α → E) (s : Set α) :
    eVariationOn (f + g) s ≤ eVariationOn f s + eVariationOn g s := by sorry

end eVariationOn
