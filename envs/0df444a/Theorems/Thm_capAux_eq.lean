-- Prove2me | Theorems.Thm_capAux_eq
-- name    : capAux_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:38.228302+00:00
-- url     : https://prove2.me/theorems/74c9fc33-c4b2-5011-9494-7af2e55b9e48
-- title:
--   cap Aux eq: cap Aux eq
-- statement:
--   The cap Aux eq construction uses the cap Aux eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L329-L346
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L329-L346

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

theorem capAux_eq {Z : Type*} [TopologicalSpace Z]
    (π : (ℕ → ℕ) → Z) (m : Set Z → ℝ≥0∞)
    (hsup : ∀ s : ℕ → Set Z, Monotone s → m (⋃ k, s k) = ⨆ k, m (s k))
    {c : ℝ≥0∞} (h0 : c < m (capKernel π)) :
    ∀ n i, i < n → (capAux π m hsup h0 n).val i = capBound π m hsup h0 i := by sorry
