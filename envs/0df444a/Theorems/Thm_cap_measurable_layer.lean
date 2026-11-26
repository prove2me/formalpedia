-- Prove2me | Theorems.Thm_cap_measurable_layer
-- name    : cap_measurable_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:48.223921+00:00
-- url     : https://prove2.me/theorems/f0409db0-0105-4d5c-8ae3-31d4d6d5b2fc
-- title:
--   cap measurable layer: cap measurable layer
-- statement:
--   Borel measurability of one layer of the parametrized construction:
--       the bound `β` acts through finitely many coordinates, so the layer is a
--       countable union of measurable rectangles.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L517-L549
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L517-L549

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
open ProbabilityTheory
variable {X Y : Type*}
  [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
omit [PolishSpace X]

theorem cap_measurable_layer
    (π : (ℕ → ℕ) → (X × Y)) (κ : Kernel X Y) [IsSFiniteKernel κ]
    (q : ℝ≥0∞) (n : ℕ) :
    MeasurableSet {p : X × (ℕ → ℕ) |
      q < κ p.1 (Prod.mk p.1 ⁻¹' capW π p.2 n)} := by sorry
