-- Prove2me | Theorems.Thm_probabilityMeasure_couplings_toMeasure_eq
-- name    : probabilityMeasure_couplings_toMeasure_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:05:36.541796+00:00
-- url     : https://prove2.me/theorems/e5ca0aa3-b47c-4874-8558-02aefd7d23f8
-- title:
--   probability Measure couplings to Measure eq: probability Measure couplings to Measure eq
-- statement:
--   The coupling set stated with `Measure.map` constraints on the underlying measures
--   (the shape used by `CouplingSet₀` and `MultiPeriod.Feas`) coincides with the coupling
--   set stated via `ProbabilityMeasure.map` (verbatim copy of F2 — dedupe at integration).
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsCompact.lean#L92-L102
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsCompact.lean#L92-L102

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
set_option autoImplicit false
open MeasureTheory Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]
omit [TopologicalSpace A] [PolishSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [BorelSpace B]

theorem probabilityMeasure_couplings_toMeasure_eq
    (mu : ProbabilityMeasure A) (nu : ProbabilityMeasure B) :
    {γ : ProbabilityMeasure (A × B) |
        (γ : Measure (A × B)).map Prod.fst = (mu : Measure A) ∧
        (γ : Measure (A × B)).map Prod.snd = (nu : Measure B)}
      = {γ : ProbabilityMeasure (A × B) |
          γ.map measurable_fst.aemeasurable = mu ∧
          γ.map measurable_snd.aemeasurable = nu} := by sorry
