-- Prove2me | Theorems.Thm_iInter_capW_subset
-- name    : iInter_capW_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:01:48.53345+00:00
-- url     : https://prove2.me/theorems/c07ef16d-1bab-48dd-8b8e-c025bd12026c
-- title:
--   i Inter cap W subset: i Inter cap W subset
-- statement:
--   **Core lemma.** For continuous `π` and any bound `β`, the decreasing
--       intersection of the bounded approximations is contained in the compact
--       set `π '' Σ(β)`. Proved by subsequence extraction in `Σ(β)`.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L180-L231
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L180-L231

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
variable {Z : Type*} [TopologicalSpace Z]

theorem iInter_capW_subset {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    {π : (ℕ → ℕ) → Z} (hπ : Continuous π) (β : ℕ → ℕ) :
    (⋂ n, capW π β n) ⊆ π '' capBelow β := by sorry
