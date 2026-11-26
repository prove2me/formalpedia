-- Prove2me | Theorems.Thm_exists_eps_optimal_selector
-- name    : exists_eps_optimal_selector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:12:25.69482+00:00
-- url     : https://prove2.me/theorems/1ffebbac-c118-4630-b89e-807b1aaeed15
-- title:
--   exists eps optimal selector: exists eps optimal selector
-- statement:
--   **ε-optimal analytically measurable selection** (Bertsekas–Shreve,
--       Proposition 7.50 analogue, ε-optimal half, in `ℝ≥0∞`). If `Γ ⊆ H × E`
--       is analytic with nonempty fibers (H, E Polish) and `F` is lower
--       semianalytic on the product, then for every `ε > 0` there is a
--       σ(Σ¹₁)-measurable selector that is everywhere feasible and everywhere
--       ε-optimal for the fiber infimum.
--
--       Proof: normalize `ε' := min ε 1`; partition the domain into the bands
--       `{g = ∞}` and `{m·ε' ≤ g < (m+1)·ε'}` of the fiber infimum `g` (lower
--       semianalytic by BS 7.47, so all bands are σ(Σ¹₁)); on band `m` select
--       from the analytic set `Γ ∩ {F < (m+1)·ε'}` via Jankov–von Neumann; on
--       the infinite band any feasible selection is ε-optimal; glue with
--       `AnalyticallyMeasurable.find`.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/EpsOptimalSelection.lean#L148-L236
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/EpsOptimalSelection.lean#L148-L236

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Definitions.Def_BicausalOT_DescriptiveSetTheory_EpsOptimalSelection
set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
noncomputable section
variable {H E : Type*} [TopologicalSpace H] [TopologicalSpace E]
open EpsOptimalSelection

theorem exists_eps_optimal_selector [PolishSpace H] [PolishSpace E]
    {Γ : Set (H × E)} {F : H × E → ℝ≥0∞}
    (hΓ : AnalyticSet Γ) (hF : IsLowerSemianalytic (X := H × E) F)
    (hfib : ∀ h : H, ∃ e : E, (h, e) ∈ Γ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ φ : H → E, AnalyticallyMeasurable φ ∧ (∀ h, (h, φ h) ∈ Γ) ∧
      ∀ h, F (h, φ h) ≤ (⨅ (e : E) (_ : (h, e) ∈ Γ), F (h, e)) + ε := by sorry
