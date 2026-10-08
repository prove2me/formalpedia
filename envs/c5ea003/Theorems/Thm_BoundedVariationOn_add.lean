-- Prove2me | Theorems.Thm_BoundedVariationOn_add
-- name    : BoundedVariationOn.add
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-10-04T23:45:16.694606+00:00
-- url     : https://prove2.me/theorems/ec9fcbf7-f3aa-49e5-8de9-e54854c9b5a7
-- title:
--   Sums of bounded-variation functions have bounded variation
-- statement:
--   Sums of bounded-variation functions have bounded variation.
-- source:
--   https://github.com/deancureton/MovingSofa

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.Compact

namespace BoundedVariationOn

theorem add {α E : Type*} [LinearOrder α]
    [SeminormedAddCommGroup E] {f g : α → E} {s : Set α}
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (f + g) s := by sorry

end BoundedVariationOn
