-- Prove2me | Theorems.Thm_ReweightedNPMLE_integral_abs_le_sqrt_weightedL2
-- name    : ReweightedNPMLE.integral_abs_le_sqrt_weightedL2
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:40:44.921109+00:00
-- url     : https://prove2.me/theorems/d0ddb05a-891e-5b7d-8ace-2cb3f2dd2386
-- title:
--   Weighted Cauchy–Schwarz from weighted squared error to absolute error
-- statement:
--   Let $\mu$ be a measure and let $h,\phi$ be real-valued functions that are almost-everywhere strongly measurable. Suppose $\phi>0$ almost everywhere, and both $h^2/\phi$ and $\phi$ are integrable. Then $$\int|h|\,d\mu\le\left(\int\frac{h^2}{\phi}\,d\mu\right)^{1/2}\left(\int\phi\,d\mu\right)^{1/2}.$$ Normalization of $\phi$ is not required. This converts Gaussian weighted $L^2$ approximation into $L^1$ control.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/Hellinger.lean#L75-L133

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

theorem ReweightedNPMLE.integral_abs_le_sqrt_weightedL2
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (h φ : Ω → ℝ)
    (hh : AEStronglyMeasurable h μ) (hφm : AEStronglyMeasurable φ μ)
    (hφpos : ∀ᵐ x ∂μ, 0 < φ x)
    (hweighted : Integrable (fun x ↦ h x ^ 2 / φ x) μ)
    (hφint : Integrable φ μ) :
    ∫ x, |h x| ∂μ ≤
      (∫ x, h x ^ 2 / φ x ∂μ) ^ (1 / 2 : ℝ) *
        (∫ x, φ x ∂μ) ^ (1 / 2 : ℝ) := by sorry
