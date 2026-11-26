-- Prove2me | Theorems.Thm_isClosed_couplings_hit
-- name    : isClosed_couplings_hit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:09:24.668166+00:00
-- url     : https://prove2.me/theorems/351f8a39-2614-5576-9cf4-2da7e381123f
-- title:
--   is Closed couplings hit: is Closed couplings hit
-- statement:
--   **Closed hit-sets (E3-B).** For a closed set `C` of joint laws, the
--       set of marginal pairs whose couplings meet `C` is closed.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsUHC.lean#L143-L159
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsUHC.lean#L143-L159

import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
set_option autoImplicit false
open MeasureTheory Set Filter Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]

theorem isClosed_couplings_hit
    {C : Set (ProbabilityMeasure (A × B))} (hC : IsClosed C) :
    IsClosed {p : ProbabilityMeasure A × ProbabilityMeasure B |
      ∃ γ ∈ C, (γ : Measure (A × B)).map Prod.fst = (p.1 : Measure A) ∧
        (γ : Measure (A × B)).map Prod.snd = (p.2 : Measure B)} := by sorry
