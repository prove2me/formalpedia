-- Prove2me | Theorems.Thm_isCompact_probabilityMeasure_couplings_toMeasure
-- name    : isCompact_probabilityMeasure_couplings_toMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:05:42.480468+00:00
-- url     : https://prove2.me/theorems/b9055cc3-409a-56a9-af4a-ccd4322a6ba2
-- title:
--   is Compact probability Measure couplings to Measure: is Compact probability Measure couplings to Measure
-- statement:
--   **F3, `Measure` level, `ProbabilityMeasure` targets.** The set of probability
--   measures on `A × B` whose underlying measure has marginals `mu` and `nu` is compact in
--   the topology of weak convergence.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsCompact.lean#L170-L176
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsCompact.lean#L170-L176

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
set_option autoImplicit false
open MeasureTheory Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]

theorem isCompact_probabilityMeasure_couplings_toMeasure
    (mu : ProbabilityMeasure A) (nu : ProbabilityMeasure B) :
    IsCompact {γ : ProbabilityMeasure (A × B) |
      (γ : Measure (A × B)).map Prod.fst = (mu : Measure A) ∧
      (γ : Measure (A × B)).map Prod.snd = (nu : Measure B)} := by sorry
