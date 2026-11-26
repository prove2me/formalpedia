-- Prove2me | Theorems.Thm_isTightMeasureSet_couplings
-- name    : isTightMeasureSet_couplings
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:05:25.014968+00:00
-- url     : https://prove2.me/theorems/1b533169-f945-5aa5-a0f0-7586fb6cdcbb
-- title:
--   is Tight Measure Set couplings: is Tight Measure Set couplings
-- statement:
--   **F3, tightness, `Measure` level.** On Borel Polish spaces, the set of measures on
--   `A × B` with marginals `mu` and `nu` is uniformly tight: `mu` and `nu` are individually
--   tight, and if `K₁`, `K₂` capture all but `ε / 2` of the mass of `mu`, `nu` respectively,
--   then `K₁ ×ˢ K₂` captures all but `ε` of the mass of every coupling, by the marginal
--   equations.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsCompact.lean#L111-L134
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsCompact.lean#L111-L134

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
set_option autoImplicit false
open MeasureTheory Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]

theorem isTightMeasureSet_couplings
    (mu : ProbabilityMeasure A) (nu : ProbabilityMeasure B) :
    IsTightMeasureSet {γm : Measure (A × B) |
      γm.map Prod.fst = (mu : Measure A) ∧ γm.map Prod.snd = (nu : Measure B)} := by sorry
