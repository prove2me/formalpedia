-- Prove2me | Theorems.Thm_isTightMeasureSet_probabilityMeasure_couplings
-- name    : isTightMeasureSet_probabilityMeasure_couplings
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:05:35.063488+00:00
-- url     : https://prove2.me/theorems/9040960f-8c17-5941-83e0-5bc060c98b27
-- title:
--   is Tight Measure Set probability Measure couplings: is Tight Measure Set probability Measure couplings
-- statement:
--   **F3, tightness, image form.** The underlying measures of the coupling set of `mu`
--   and `nu` form a tight set of measures — the exact hypothesis shape of Prokhorov's
--   theorem `isCompact_closure_of_isTightMeasureSet`.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsCompact.lean#L139-L148
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsCompact.lean#L139-L148

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
set_option autoImplicit false
open MeasureTheory Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]

theorem isTightMeasureSet_probabilityMeasure_couplings
    (mu : ProbabilityMeasure A) (nu : ProbabilityMeasure B) :
    IsTightMeasureSet {((γ : ProbabilityMeasure (A × B)) : Measure (A × B)) |
      γ ∈ {γ' : ProbabilityMeasure (A × B) |
        γ'.map measurable_fst.aemeasurable = mu ∧
        γ'.map measurable_snd.aemeasurable = nu}} := by sorry
