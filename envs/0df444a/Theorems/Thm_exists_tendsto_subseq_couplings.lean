-- Prove2me | Theorems.Thm_exists_tendsto_subseq_couplings
-- name    : exists_tendsto_subseq_couplings
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:09:45.367296+00:00
-- url     : https://prove2.me/theorems/7bae7886-9f77-427b-849a-37bbf072d322
-- title:
--   exists tendsto subseq couplings: exists tendsto subseq couplings
-- statement:
--   **Sequential upper hemicontinuity.** Along convergent marginal
--       sequences, any sequence of couplings admits a subsequence converging
--       to a coupling of the limit marginals (tightness + Prokhorov +
--       continuity of the marginal maps).
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsUHC.lean#L84-L137
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsUHC.lean#L84-L137

import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
set_option autoImplicit false
open MeasureTheory Set Filter Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]

theorem exists_tendsto_subseq_couplings
    {μs : ℕ → ProbabilityMeasure A} {μ : ProbabilityMeasure A}
    {νs : ℕ → ProbabilityMeasure B} {ν : ProbabilityMeasure B}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    {γs : ℕ → ProbabilityMeasure (A × B)}
    (hfst : ∀ n, (γs n : Measure (A × B)).map Prod.fst = (μs n : Measure A))
    (hsnd : ∀ n, (γs n : Measure (A × B)).map Prod.snd = (νs n : Measure B)) :
    ∃ γ : ProbabilityMeasure (A × B),
      (γ : Measure (A × B)).map Prod.fst = (μ : Measure A) ∧
      (γ : Measure (A × B)).map Prod.snd = (ν : Measure B) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (γs ∘ φ) atTop (𝓝 γ) := by sorry
