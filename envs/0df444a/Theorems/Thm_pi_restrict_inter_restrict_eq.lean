-- Prove2me | Theorems.Thm_pi_restrict_inter_restrict_eq
-- name    : pi_restrict_inter_restrict_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:36:07.958437+00:00
-- url     : https://prove2.me/theorems/df5755b6-155e-4927-98be-e6fb7135dc7a
-- title:
--   pi restrict inter restrict eq: pi restrict inter restrict eq
-- statement:
--   The pi restrict inter restrict eq construction uses the pi restrict inter restrict eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L120-L124
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L120-L124

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

theorem pi_restrict_inter_restrict_eq {s t : Set ι} (hi : Disjoint s t)
    (A : Set (s → Ω)) (B : Set (t → Ω)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measure.pi P (s.restrict ⁻¹' A ∩ t.restrict ⁻¹' B) =
      Measure.pi P (s.restrict ⁻¹' A) * Measure.pi P (t.restrict ⁻¹' B) := by sorry
