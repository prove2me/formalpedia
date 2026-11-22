-- Prove2me | Theorems.Thm_pi_inter_eq
-- name    : pi_inter_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:38:15.407772+00:00
-- url     : https://prove2.me/theorems/f832286a-4814-4017-8045-f21fe47edada
-- title:
--   pi inter eq: pi inter eq
-- statement:
--   The pi inter eq construction uses the pi inter eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L139-L151
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L139-L151

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

theorem pi_inter_eq (s t : Set ι) (hst : Disjoint s t)
    (A B : Set (ι → Ω)) (hs : DependsOn (· ∈ A) s) (ht : DependsOn (· ∈ B) t)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measure.pi P (A ∩ B) = Measure.pi P A * Measure.pi P B := by sorry
