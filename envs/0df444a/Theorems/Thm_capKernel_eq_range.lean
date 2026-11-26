-- Prove2me | Theorems.Thm_capKernel_eq_range
-- name    : capKernel_eq_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:01:53.290804+00:00
-- url     : https://prove2.me/theorems/6710ce44-6a9e-5e63-9491-11536c547c92
-- title:
--   cap Kernel eq range: cap Kernel eq range
-- statement:
--   The Souslin kernel of the canonical scheme recovers exactly the range:
--       the nontrivial inclusion is via the core lemma with `β := σ`.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L280-L291
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L280-L291

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

theorem capKernel_eq_range {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    {π : (ℕ → ℕ) → Z} (hπ : Continuous π) : capKernel π = range π := by sorry
