-- Prove2me | Theorems.Thm_isCompact_probabilityMeasure_marginals
-- name    : isCompact_probabilityMeasure_marginals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:08:10.715886+00:00
-- url     : https://prove2.me/theorems/e0c1abb7-5f0d-5ebc-8f30-a6cbca203337
-- title:
--   is Compact probability Measure marginals: is Compact probability Measure marginals
-- statement:
--   **F3, `Measure` level, plain `Measure` targets, unconditional.** For arbitrary
--   target measures `m`, `n` (the exact shape of `MultiPeriod.Feas` and `CouplingSet₀`,
--   reindexed over probability measures on the product), the constraint set is compact in
--   the topology of weak convergence: if either target fails to be a probability measure
--   the set is empty, and the empty set is compact.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsCompact.lean#L183-L208
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsCompact.lean#L183-L208

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
set_option autoImplicit false
open MeasureTheory Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]

theorem isCompact_probabilityMeasure_marginals (m : Measure A) (n : Measure B) :
    IsCompact {γ : ProbabilityMeasure (A × B) |
      (γ : Measure (A × B)).map Prod.fst = m ∧ (γ : Measure (A × B)).map Prod.snd = n} := by sorry
