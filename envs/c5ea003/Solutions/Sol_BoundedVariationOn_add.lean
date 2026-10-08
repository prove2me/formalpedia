-- Prove2me | solution 1 for BoundedVariationOn.add
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-10-04T23:50:16.224333+00:00
-- url     : https://prove2.me/submissions/8f5f6c50-839f-4a7a-bce0-faf409e8c13b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.Compact
import Theorems.Thm_eVariationOn_add_le


/-- A sum of two functions of bounded variation has bounded variation. -/
theorem solution {α E : Type*} [LinearOrder α]
    [SeminormedAddCommGroup E] {f g : α → E} {s : Set α}
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (f + g) s := by
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) ?_
  exact eVariationOn.add_le f g s
