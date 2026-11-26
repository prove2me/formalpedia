-- Prove2me | Theorems.Thm_measurableSet_couplings_hit
-- name    : measurableSet_couplings_hit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:13:59.862419+00:00
-- url     : https://prove2.me/theorems/ec1278cd-bb7b-5f9f-bb49-a6c4545fc079
-- title:
--   measurable Set couplings hit: measurable Set couplings hit
-- statement:
--   **Borel hit-sets (E3-C).** For an open set `U` of joint laws, the set
--       of marginal pairs whose couplings meet `U` is Borel — with respect to
--       Borel σ-algebras of the weak topology on the factors (σ-algebra
--       polymorphic via the `BorelSpace` constraints; NOT Mathlib's
--       Giry-subtype σ-algebra). Decompose `U` into countably many closed
--       sets and take the union of the closed hit-sets.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsUHC.lean#L193-L218
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsUHC.lean#L193-L218

import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
set_option autoImplicit false
open MeasureTheory Set Filter Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]

theorem measurableSet_couplings_hit
    {mPA : MeasurableSpace (ProbabilityMeasure A)}
    [BorelSpace (ProbabilityMeasure A)]
    {mPB : MeasurableSpace (ProbabilityMeasure B)}
    [BorelSpace (ProbabilityMeasure B)]
    {U : Set (ProbabilityMeasure (A × B))} (hU : IsOpen U) :
    MeasurableSet {p : ProbabilityMeasure A × ProbabilityMeasure B |
      ∃ γ ∈ U, (γ : Measure (A × B)).map Prod.fst = (p.1 : Measure A) ∧
        (γ : Measure (A × B)).map Prod.snd = (p.2 : Measure B)} := by sorry
