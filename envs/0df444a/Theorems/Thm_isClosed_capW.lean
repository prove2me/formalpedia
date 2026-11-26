-- Prove2me | Theorems.Thm_isClosed_capW
-- name    : isClosed_capW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:01:41.991094+00:00
-- url     : https://prove2.me/theorems/7fbe1cb0-7e16-570f-b2c8-da79ec6b7c9d
-- title:
--   is Closed cap W: is Closed cap W
-- statement:
--   The is Closed cap W construction uses the is Closed cap W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L157-L159
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L157-L159

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

theorem isClosed_capW (π : (ℕ → ℕ) → Z) (β : ℕ → ℕ) (n : ℕ) :
    IsClosed (capW π β n) := by sorry
