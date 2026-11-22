-- Prove2me | Theorems.Thm_indepFrom_iff_indepSets
-- name    : indepFrom_iff_indepSets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:36:55.800237+00:00
-- url     : https://prove2.me/theorems/320c898c-15f4-4dcd-b905-fecfedcfcc5a
-- title:
--   indep From iff indep Sets: indep From iff indep Sets
-- statement:
--   The indep From iff indep Sets construction uses the indep From iff indep Sets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LocalLemma.lean#L63-L73
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LocalLemma.lean#L63-L73

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_LocalLemma
set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
open MeasurableSpace Measure
variable {s : Set Ω} {t t' : Set (Set Ω)}

theorem indepFrom_iff_indepSets {P : Measure Ω} [IsZeroOrProbabilityMeasure P]
    {s : Set Ω} {t : Set (Set Ω)} (hs : MeasurableSet s) (ht : ∀ i ∈ t, MeasurableSet i) :
    IndepFrom s t P ↔ IndepSets {s} (generatePiSystem t) P := by sorry
