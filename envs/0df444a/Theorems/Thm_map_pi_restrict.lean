-- Prove2me | Theorems.Thm_map_pi_restrict
-- name    : map_pi_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:38:00.535307+00:00
-- url     : https://prove2.me/theorems/a0be5969-2fc8-4bfc-899d-a8a58ffee0d8
-- title:
--   map pi restrict: map pi restrict
-- statement:
--   The map pi restrict construction uses the map pi restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L89-L109
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L89-L109

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc
set_option autoImplicit true
open Finset
open MeasureTheory Measure ProbabilityTheory
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : ι → Measure Ω}
variable [∀ i, IsProbabilityMeasure (P i)] {s : Set ι}
open Classical

theorem map_pi_restrict (i₁ : Set ι) :
    (Measure.pi P).map i₁.restrict = Measure.pi (fun i : i₁ ↦ P i) := by sorry
