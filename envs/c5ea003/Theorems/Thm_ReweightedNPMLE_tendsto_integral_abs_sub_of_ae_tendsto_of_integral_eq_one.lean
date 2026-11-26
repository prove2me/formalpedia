-- Prove2me | Theorems.Thm_ReweightedNPMLE_tendsto_integral_abs_sub_of_ae_tendsto_of_integral_eq_one
-- name    : ReweightedNPMLE.tendsto_integral_abs_sub_of_ae_tendsto_of_integral_eq_one
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:46:51.116333+00:00
-- url     : https://prove2.me/theorems/502c334e-ba7f-449f-8643-91bddd3b0b89
-- title:
--   Scheffé’s lemma for real probability densities
-- statement:
--   Let $p_n$ and $q$ be almost-everywhere strongly measurable, nonnegative, integrable functions on a measure space, each with integral one. If $p_n(x)\to q(x)$ almost everywhere, then $$\int|p_n-q|\,d\mu\longrightarrow0.$$ This form of Scheffé’s lemma upgrades pointwise convergence of mixture densities to $L^1$ convergence.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/Hellinger.lean#L328-L384

import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Hellinger

/-!
# Squared Hellinger distance

This file formalizes the normalization convention used in the manuscript,
`H²(p,q) = ∫ (√p-√q)²`, and its affinity identity.
-/

open MeasureTheory Filter Topology

open ReweightedNPMLE

theorem ReweightedNPMLE.tendsto_integral_abs_sub_of_ae_tendsto_of_integral_eq_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : ℕ → Ω → ℝ) (q : Ω → ℝ)
    (hpmeas : ∀ n, AEStronglyMeasurable (p n) μ)
    (hqmeas : AEStronglyMeasurable q μ)
    (hp : ∀ n, ∀ᵐ x ∂μ, 0 ≤ p n x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hpint : ∀ n, Integrable (p n) μ) (hqint : Integrable q μ)
    (hpone : ∀ n, ∫ x, p n x ∂μ = 1) (hqone : ∫ x, q x ∂μ = 1)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ p n x) atTop (𝓝 (q x))) :
    Tendsto (fun n ↦ ∫ x, |p n x - q x| ∂μ) atTop (𝓝 0) := by sorry
