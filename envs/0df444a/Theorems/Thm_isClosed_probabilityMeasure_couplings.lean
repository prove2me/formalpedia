-- Prove2me | Theorems.Thm_isClosed_probabilityMeasure_couplings
-- name    : isClosed_probabilityMeasure_couplings
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:05:20.554847+00:00
-- url     : https://prove2.me/theorems/6f895d6c-7e20-5eec-9e7a-e2c37b264b75
-- title:
--   is Closed probability Measure couplings: is Closed probability Measure couplings
-- statement:
--   **F2, `ProbabilityMeasure` level** (verbatim copy — dedupe at integration). On Borel
--   Polish spaces, the set of couplings of `mu` and `nu` is closed in the topology of weak
--   convergence.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsCompact.lean#L75-L85
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsCompact.lean#L75-L85

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
set_option autoImplicit false
open MeasureTheory Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]

theorem isClosed_probabilityMeasure_couplings
    (mu : ProbabilityMeasure A) (nu : ProbabilityMeasure B) :
    IsClosed {γ : ProbabilityMeasure (A × B) |
      γ.map measurable_fst.aemeasurable = mu ∧ γ.map measurable_snd.aemeasurable = nu} := by sorry
