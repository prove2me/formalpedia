-- Prove2me | Theorems.Thm_isTightMeasureSet_couplings_of_isTightMeasureSet
-- name    : isTightMeasureSet_couplings_of_isTightMeasureSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:08:49.162045+00:00
-- url     : https://prove2.me/theorems/c4b656bc-7c67-50ff-878f-defa7e5ba0fb
-- title:
--   is Tight Measure Set couplings of is Tight Measure Set: is Tight Measure Set couplings of is Tight Measure Set
-- statement:
--   Couplings whose marginals range over tight families form a tight
--       family: the slab bound `γ ((K₁ ×ˢ K₂)ᶜ) ≤ μ K₁ᶜ + ν K₂ᶜ`.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsUHC.lean#L58-L76
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsUHC.lean#L58-L76

import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
set_option autoImplicit false
open MeasureTheory Set Filter Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]

theorem isTightMeasureSet_couplings_of_isTightMeasureSet
    {S : Set (Measure A)} {T : Set (Measure B)}
    (hS : IsTightMeasureSet S) (hT : IsTightMeasureSet T) :
    IsTightMeasureSet
      {γm : Measure (A × B) | γm.map Prod.fst ∈ S ∧ γm.map Prod.snd ∈ T} := by sorry
