-- Prove2me | Theorems.Thm_standardCondition_of
-- name    : standardCondition_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:37:22.776285+00:00
-- url     : https://prove2.me/theorems/324acce8-a198-42ea-96c3-093e21eb4d94
-- title:
--   standard Condition of: standard Condition of
-- statement:
--   A way to construct the standard condition from independence structure of random variables.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LocalLemma.lean#L311-L361
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LocalLemma.lean#L311-L361

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_LocalLemma
set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {A : ι → Set Ω} {N : ι → Finset ι} {x : ι → ℝ} {i j : ι} {S T : Finset ι}
open Finset

theorem standardCondition_of {α β : Type*} [Finite ι] [MeasurableSpace β] [IsProbabilityMeasure P]
    (I : α → Ω → β) {A : ι → Set Ω} {N : ι → Finset ι} (D : ι → Finset α)
    (hND : ∀ i j, i ≠ j → i ∉ N j → Disjoint (D i) (D j))
    (hI : ∀ a : α, Measurable (I a))
    (hI' : iIndepFun I P)
    (hA : ∀ i, ∃ S : Set (α → β), MeasurableSet S ∧
      DependsOn (· ∈ S) (D i) ∧ A i = (fun ω a ↦ I a ω) ⁻¹' S) :
    standardCondition P A N := by sorry
