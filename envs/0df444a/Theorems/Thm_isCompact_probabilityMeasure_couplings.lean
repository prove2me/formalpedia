-- Prove2me | Theorems.Thm_isCompact_probabilityMeasure_couplings
-- name    : isCompact_probabilityMeasure_couplings
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:05:47.79691+00:00
-- url     : https://prove2.me/theorems/43c03a74-2cf4-4607-b82c-0477fdf01201
-- title:
--   is Compact probability Measure couplings: is Compact probability Measure couplings
-- statement:
--   **F3, MAIN TARGET.** On Borel Polish spaces, the set of couplings of `mu` and `nu`
--   is compact in the topology of weak convergence: it is tight
--   (`isTightMeasureSet_probabilityMeasure_couplings`), so its closure is compact by
--   Prokhorov's theorem, and it is closed (`isClosed_probabilityMeasure_couplings`), so it
--   equals its closure.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsCompact.lean#L157-L165
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsCompact.lean#L157-L165

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
set_option autoImplicit false
open MeasureTheory Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]

theorem isCompact_probabilityMeasure_couplings
    (mu : ProbabilityMeasure A) (nu : ProbabilityMeasure B) :
    IsCompact {γ : ProbabilityMeasure (A × B) |
      γ.map measurable_fst.aemeasurable = mu ∧ γ.map measurable_snd.aemeasurable = nu} := by sorry
