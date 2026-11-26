-- Prove2me | Theorems.Thm_cap_exists_bound
-- name    : cap_exists_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:00.170476+00:00
-- url     : https://prove2.me/theorems/faa7422d-ec9c-491b-8827-8fd8f69f8b5a
-- title:
--   cap exists bound: cap exists bound
-- statement:
--   **Bounded recursion.** From `c < m (𝒜(G))` produce a bound `β` with
--       `c < m (W(β, n))` for every `n`.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L350-L362
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L350-L362

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

theorem cap_exists_bound {Z : Type*} [TopologicalSpace Z]
    (π : (ℕ → ℕ) → Z) (m : Set Z → ℝ≥0∞)
    (hmono : ∀ ⦃S T : Set Z⦄, S ⊆ T → m S ≤ m T)
    (hsup : ∀ s : ℕ → Set Z, Monotone s → m (⋃ k, s k) = ⨆ k, m (s k))
    {c : ℝ≥0∞} (h0 : c < m (capKernel π)) :
    ∃ β : ℕ → ℕ, ∀ n, c < m (capW π β n) := by sorry
